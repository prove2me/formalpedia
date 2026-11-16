-- Prove2me | Theorems.Thm_FasterPrimeEnum_Supplement_theorem_9_1
-- name    : FasterPrimeEnum.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:55:14.67867+00:00
-- url     : https://prove2.me/theorems/4d5ff977-3680-4086-ab0f-611d673af43b
-- title:
--   Theorem 9.1 — the core algorithm with permuted vectors outputs $\kappa_\pi(a^r)$ within the bound (6.3)
-- statement:
--   There is a deterministic algorithm with the following properties. Its input is positive integers $N,T,R$ with $T\mid N$ and $R\le T/2$, and a permutation $\pi=(\pi_0,\dots,\pi_{T-1})$ of $\{0,\dots,T-1\}$. Its output is the list of vectors
--
--   $$
--   \kappa_\pi(a^r)\in\mathbb F_2^S,\qquad 0\le r<N/T,
--   $$
--
--   where $a^r$ marks the odd square-primes in $[rT,(r+1)T)$ (6.1) and $\kappa_\pi=\kappa\circ Q_\pi$ is the compression map composed with the permutation. If $\log T<C\log\log N$ for some $C>0$ (6.2), the running time is
--
--   $$
--   O_C\Big(\Big(1+\frac{R\log N}{T}\Big)N(\log\log N)^{1+o(1)}\Big).
--   $$
--
--   Randomizing $\pi$ makes an impostor vector with the same compression unlikely; this is the core step of the probabilistic algorithm (Theorem 1.3).
--
--   **Formalization Note** One machine, one output tape, one $\varepsilon\to0$ and the field data $(h,\beta)$ for each $T$ are fixed before $C$; then a constant $K$ for each $C$, before the input. The input is the framed list of $N,T,R$ in binary and of $\pi_0,\dots,\pi_{T-1}$ in binary; the output is the concatenation of the $N/T$ words of $S=2\lambda R$ bits.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) with RunsWithin / RunOutcome (a halted run within the time bound, with exactly the output on a designated tape); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a change of the O-constant or a shift of an o(1) exponent); an existential over the more restricted machine is the stronger statement
--   - encoding: input positive integers N, T, R and a permutation π; output the list of vectors κ_π(a^r) → input Encoding.encodeList id [binWord N, binWord T, binWord R, encodeList binWord [π₀, …, π_{T−1}]]; output the concatenation of the N/T words κ_π(a^r) of S bits; reason: the paper fixes no tape layout; the vectors are consecutive S-bit blocks
--   - reading: κ of Section 5 for the fixed h and β → a function fd : ℕ → FieldData chosen with the machine (before C), with IsFieldData (lam T) (fd T) for every T ≥ 1; reason: the paper's h and β depend only on λ = lg(T + 1) and are computed by the algorithm
--   - reading: O_C((1 + R log N/T) N (log log N)^{1+o(1)}) under (6.2) → one ε → 0 chosen before C, then for each C > 0 a constant K before the input; output and time stated together under log T < C·logU (logU N); reason: the shape of the published Theorem 6.1, of which this is the variant; every valid input satisfies (6.2) for some C > 0, so the output claim holds on every valid input
--   - encoding: log x and log log x in complexity bounds → logU x = log max(x, 2) and logU (logU x); reason: the paper's convention (p.2): in complexity bounds log x should be read as log max(x, 2)
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 9.1, p.87; eq. (6.1)–(6.3), p.40; §5.1, pp.35–36

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_IsSquarePrime
import Definitions.Def_FasterPrimeEnum_oddSqPrimeBlock
import Definitions.Def_FasterPrimeEnum_Supplement_kappa

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open ThreeSumApsp
open Filter Topology

/-- **Theorem 9.1 (Core algorithm with permuted vectors)** — D. Harvey, *Faster enumeration of
primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.87.

"There is a (deterministic) algorithm with the following properties. It takes as input positive
integers N, T and R such that T | N and R ⩽ T/2, and a permutation π = (π₀, …, π_{T−1}) ∈ Π_T. Its
output is the list of vectors κ_π(a^r) ∈ F₂^S, 0 ⩽ r < N/T. Assuming that (6.2) holds for some
C > 0, the running time of the algorithm is given by (6.3)."

(6.2) is `log T < C log log N` and (6.3) is `O_C((1 + R log N/T) N (log log N)^{1+o(1)})` (p.40);
`a^r` is (6.1) (published `oddSqPrimeBlock T r`); `κ_π = κ ∘ Q_π` (p.87) with `κ` of §5.1.

**Formalization Note.** The shape of the published Theorem 6.1: one machine, one output tape, one
`ε → 0` and the field data `(h, β)` for each `T` (fixing `κ`, §5.1), all before `C`; for each `C > 0`
a constant `K`, before the input. The input is the framed list of the binary words of `N, T, R` and
the framed list of `π₀, …, π_{T−1}` in binary; the output is the concatenation of the `N/T` words
`κ_π(a^r)` of `S = 2λR` bits. Output and time are stated together under (6.2), for every `C > 0`;
every valid input satisfies (6.2) for some `C`. Logarithms are clipped (p.2). -/
theorem theorem_9_1 :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (ε : ℕ → ℝ) (fd : ℕ → FieldData),
      Tendsto ε atTop (𝓝 0) ∧ (∀ T : ℕ, 0 < T → IsFieldData (lam T) (fd T)) ∧
      ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧
        ∀ N T R : ℕ, 0 < N → 0 < T → 0 < R → T ∣ N → 2 * R ≤ T →
          ∀ π : Equiv.Perm (Fin T),
          Real.log (T : ℝ) < C * logU (logU (N : ℝ)) →
          RunsWithin A out
            (Encoding.encodeList id [binWord N, binWord T, binWord R,
              Encoding.encodeList binWord (List.ofFn fun t : Fin T => ((π t : Fin T) : ℕ))])
            ((List.range (N / T)).flatMap fun r => kappa (fd T) T R (permVec π (oddSqPrimeBlock T r)))
            (K * (1 + (R : ℝ) * logU (N : ℝ) / T) * N * logU (logU (N : ℝ)) ^ (1 + ε N)) := by sorry

end Supplement

end FasterPrimeEnum
