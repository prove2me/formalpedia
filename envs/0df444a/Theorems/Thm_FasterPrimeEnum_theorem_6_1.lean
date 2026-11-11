-- Prove2me | Theorems.Thm_FasterPrimeEnum_theorem_6_1
-- name    : FasterPrimeEnum.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:15.531085+00:00
-- url     : https://prove2.me/theorems/83c5c371-021c-4b81-a2e9-481f5b9b43a6
-- title:
--   Theorem 6.1 — the core algorithm recovers every interval with at most $R$ odd square-primes
-- statement:
--   Let $a^r\in\mathbb F_2^T$ be the vector of odd square-primes in $[rT,(r+1)T)$ and $\mathrm{wt}$ the number of ones. There is an algorithm, a multitape Turing machine, with the following properties. It takes as input positive integers $N$, $T$ and $R$ with $T\mid N$ and $R\le T/2$. Its output is a list of candidates
--
--   $$
--   c^r\in\mathbb F_2^T,\qquad 0\le r<N/T,
--   $$
--
--   with $\mathrm{wt}(c^r)\le R$, such that $c^r=a^r$ whenever $\mathrm{wt}(a^r)\le R$. If $\log T<C\log\log N$ for some $C>0$, its running time is
--
--   $$
--   O_C\Big(\Big(1+\frac{R\log N}{T}\Big)N(\log\log N)^{1+o(1)}\Big).
--   $$
--
--   This is the core of all three prime enumeration algorithms of the paper: it finds the odd square-primes of every interval that does not hold too many of them, and the other algorithms only have to detect and repair the exceptional intervals.
--
--   **Formalization Note** One machine, one output tape and one function $\varepsilon(N)\to0$ for the $o(1)$, all fixed first; then for each $C>0$ a constant $K$, before every input. The input is the framed triple of the binary words of $N,T,R$, and the output is the concatenation $c^0c^1\cdots c^{N/T-1}$ of $T$-bit blocks. Correctness and time are stated together under $\log T<C\log\log N$, with clipped logarithms; every valid input meets this for some $C$, so correctness holds on every valid input.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) and RunsWithin (a halted run with exactly the output on a designated tape, within the time bound); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a constant factor is a shift of the exponent's o(1), or a change of the O-constant); an existential over the more restricted machine is the stronger statement
--   - encoding: input positive integers N, T, R; output a list of candidates c^r ∈ F₂^T → input Encoding.encodeList id [binWord N, binWord T, binWord R]; output the concatenation of the N/T candidate blocks of T bits (List.flatMap); reason: the paper fixes no tape layout; the candidates are recoverable from the word as consecutive T-bit blocks
--   - reading: O_C((1 + R log N/T) N (log log N)^{1+o(1)}) → one ε → 0 chosen before C, then for each C > 0 a constant K before the input; reason: the proof's o(1) comes from M*(N), K*(N), R*(B) and log log log N (pp.56–57) and does not depend on C, while C enters only the constant; the stronger of the two readings
--   - encoding: correctness for all valid inputs, time under (6.2) → correctness and time both stated under log T < C·logU (logU N), for every C > 0; reason: every valid input satisfies (6.2) for some C > 0 (logU (logU N) ≥ log 2 > 0), so correctness on all valid inputs follows
--   - encoding: log x in complexity bounds → logU x = log max(x, 2) (the published ThreeSumApsp.logU), and log log x as logU (logU x); reason: the paper's convention (p.2): log x should be read as log max(x, 2); it changes no bound for large inputs
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 6.1, p.40; eq. (6.1), p.40

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_IsSquarePrime
import Definitions.Def_FasterPrimeEnum_oddSqPrimeBlock

set_option autoImplicit false

namespace FasterPrimeEnum

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open ThreeSumApsp
open Filter Topology

/-- **Theorem 6.1 (The core algorithm)** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.40.

"There is an algorithm with the following properties. It takes as input positive integers N, T
and R such that T | N and R ⩽ T/2. Its output is a list of candidates c^r ∈ F₂^T, 0 ⩽ r < N/T
with wt(c^r) ⩽ R. For each candidate, if wt(a^r) ⩽ R, then c^r = a^r. Assuming that
(6.2) log T < C log log N for some C > 0, the running time of the algorithm is
(6.3) O_C((1 + R log N/T) N (log log N)^{1+o(1)})."

Here `a^r` is the vector (6.1) of odd square-primes in `[rT, (r+1)T)` (`oddSqPrimeBlock T r`), and
`wt` is the number of ones (`count true`).

**Formalization Note.** One machine, one output tape and one `ε → 0` (the `o(1)`) before `C`; the
implied constant `K` after `C` (the `O_C`) and before the input. The input is the framed triple of
binary words of `N, T, R`. The output is the concatenation `c⁰ c¹ ⋯ c^{N/T−1}` of the candidates,
each a list of `T` bits. A candidate with `wt(a^r) > R` is any vector of weight at most `R`, so the
output is asserted to exist rather than given by a formula. Correctness is stated together with the
time bound under (6.2); every valid input satisfies (6.2) for some `C > 0` (as `logU (logU N) > 0`), so
correctness holds on every valid input. `R ⩽ T/2` is `2R ⩽ T`. Logarithms are clipped (p.2): `logU u = log max(u, 2)`. -/
theorem theorem_6_1 :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (ε : ℕ → ℝ),
      Tendsto ε atTop (𝓝 0) ∧
      ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧
        ∀ N T R : ℕ, 0 < N → 0 < T → 0 < R → T ∣ N → 2 * R ≤ T →
          Real.log (T : ℝ) < C * logU (logU (N : ℝ)) →
          ∃ c : ℕ → List Bool,
            (∀ r < N / T, (c r).length = T ∧ (c r).count true ≤ R ∧
              ((oddSqPrimeBlock T r).count true ≤ R → c r = oddSqPrimeBlock T r)) ∧
            RunsWithin A out (Encoding.encodeList id [binWord N, binWord T, binWord R])
              ((List.range (N / T)).flatMap c)
              (K * (1 + (R : ℝ) * logU (N : ℝ) / T) * N * logU (logU (N : ℝ)) ^ (1 + ε N)) := by sorry

end FasterPrimeEnum
