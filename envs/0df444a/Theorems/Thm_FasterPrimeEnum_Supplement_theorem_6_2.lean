-- Prove2me | Theorems.Thm_FasterPrimeEnum_Supplement_theorem_6_2
-- name    : FasterPrimeEnum.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:54:01.382191+00:00
-- url     : https://prove2.me/theorems/4325d2f7-476f-4d25-8baa-7e2e4e1170de
-- title:
--   Theorem 6.2 — the core algorithm with explicit block size $M$ and slicing parameter $W$, cost (6.5)
-- statement:
--   Fix a multiplication algorithm (cost $M$, with (4.2)), a transform scheme with $T(n)\ll M(n)$, and a restricted product algorithm with $R(n)\gg M(n)$ (4.10). There is an algorithm with the following properties. Its input is positive integers $N,T,R,M,W$ with
--
--   $$
--   T\mid W,\qquad W\mid M,\qquad M\mid N,\qquad R\le T/2.
--   $$
--
--   Its output is a list of candidates $c^r\in\mathbb F_2^T$, $0\le r<N/T$, with $\mathrm{wt}(c^r)\le R$, such that $c^r=a^r$ whenever $\mathrm{wt}(a^r)\le R$; here $a^r$ marks the odd square-primes in $[rT,(r+1)T)$. With $B:=N/M$, its running time is
--
--   $$
--   \begin{aligned}
--   O\Big(&N\frac{R\log T\log N}{T}M^*(N)+N\frac{\rho(W)\log N}{W}M^*(N)+(M+B)\log^3N\\
--   &+N\log W\cdot M^*(W)K^*(N)+N\log B\cdot R^*(B)K^*(W)K^*(N)\\
--   &+\Big(1+\frac{R(\log T)^{4+o(1)}}{T}\Big)N\log T\cdot C^*(T)K^*(N)+T(\log T)^{3+o(1)}\Big),
--   \end{aligned}
--   $$
--
--   where $\rho(W)$ is (6.32) and $C^*=M^*+K^*$.
--
--   Theorem 6.1 follows by choosing $M$ and $W$; the explicit form shows which step dominates in each of the three prime enumeration algorithms.
--
--   **Formalization Note** One machine, one output tape, $\varepsilon_1,\varepsilon_2\to0$ (functions of $T$) and one constant $K$, before the input; the input is the framed list of the binary words of $N,T,R,M,W$ and the output the concatenation of the candidate blocks.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) with RunsWithin / RunOutcome (a halted run within the time bound, with exactly the output on a designated tape); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a change of the O-constant or a shift of an o(1) exponent); an existential over the more restricted machine is the stronger statement
--   - reading: the algorithms fixed in §4.1, §4.3, §4.4 ("we fix …") with the standing assumption (4.2) M(kn) ≪_k M(n) (p.19) → the statement holds for every multiplication algorithm Mul with Mul.Assumption42 and every transform scheme with T(n) ≤ c·M(n) and every restricted product algorithm with M(n) ≤ c'·R(n) ((4.10)); reason: the paper fixes arbitrary such algorithms and assumes (4.2) and (4.10) for the rest of the paper (pp.19, 27, 36); a universal quantifier is exactly "for the fixed ones, whichever they are"
--   - encoding: input positive integers N, T, R, M, W; output a list of candidates c^r ∈ F₂^T → input Encoding.encodeList id [binWord N, binWord T, binWord R, binWord M, binWord W]; output the concatenation of the N/T candidate blocks of T bits; reason: the paper fixes no tape layout; the candidates are consecutive T-bit blocks of the word
--   - encoding: the two o(1) terms inside (6.5) → two functions ε₁, ε₂ : ℕ → ℝ of T tending to 0; reason: both come from Theorems 5.2 and 5.5 and are o(1) as T → ∞
--   - encoding: log x and log log x in complexity bounds → logU x = log max(x, 2) and logU (logU x); reason: the paper's convention (p.2): in complexity bounds log x should be read as log max(x, 2)
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 6.2, pp.40–41; eq. (6.1), p.40; eq. (6.32), p.48

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_IsSquarePrime
import Definitions.Def_FasterPrimeEnum_oddSqPrimeBlock
import Definitions.Def_FasterPrimeEnum_H
import Definitions.Def_FasterPrimeEnum_Supplement_MulAlgorithm
import Definitions.Def_FasterPrimeEnum_Supplement_TransformScheme
import Definitions.Def_FasterPrimeEnum_Supplement_RestrictedProductAlgorithm
import Definitions.Def_FasterPrimeEnum_Supplement_rho

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open ThreeSumApsp
open Filter Topology

/-- **Theorem 6.2** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version,
sha256 7fc13f17…), pp.40–41.

"There is an algorithm with the following properties. It takes as input positive integers N, T, R,
M and W such that (6.4) T | W, W | M, M | N, R ⩽ T/2. Its output is a list of candidates
c^r ∈ F₂^T, 0 ⩽ r < N/T with wt(c^r) ⩽ R. For each candidate, if wt(a^r) ⩽ R, then c^r = a^r. The
running time of the algorithm is
(6.5) O( N (R log T log N / T) M*(N) + N (ρ(W) log N / W) M*(N) + (M + B) log³ N
+ N log W · M*(W) K*(N) + N log B · R*(B) K*(W) K*(N)
+ (1 + R(log T)^{4+o(1)} / T) N log T · C*(T) K*(N) + T(log T)^{3+o(1)} )
where B := N/M and where the quantity ρ(W) is defined as in (6.32)."

Here `a^r` is the vector (6.1) of odd square-primes in `[rT, (r+1)T)` (published
`oddSqPrimeBlock T r`), `wt` the number of ones, `ρ(W)` is (6.32), and `M*`, `K*`, `R*`,
`C* = M* + K*` are the cost functions of the fixed multiplication algorithm, transform scheme and
restricted product algorithm (§4.1, §4.3, §4.4, §5.2).

**Formalization Note.** Relative to every multiplication algorithm with (4.2), every transform
scheme with `T(n) ≤ c M(n)` (p.27) and every restricted product algorithm with (4.10)
`M(n) ≤ c' R(n)` (p.27): one machine, one output tape, `ε₁, ε₂ → 0` (the two `o(1)`, functions of
`T`) and one constant `K`, all before the input. The block size `M` is `Mb`. The input is the framed
list of the binary words of `N, T, R, M, W`; the output is the concatenation of the `N/T`
candidate blocks of `T` bits. A candidate with `wt(a^r) > R` is any vector of weight at most `R`, so
the output is asserted to exist. All seven terms of (6.5) are inside the one `O`; logarithms are
clipped (p.2). -/
theorem theorem_6_2 (Mul : MulAlgorithm) (hMul : Mul.Assumption42) (TS : TransformScheme)
    (hT : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → TS.Tcost n ≤ c * Mul.Mcost n)
    (RP : RestrictedProductAlgorithm)
    (hR : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → Mul.Mcost n ≤ c * RP.Rcost n) :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (ε₁ ε₂ : ℕ → ℝ) (K : ℝ),
      Tendsto ε₁ atTop (𝓝 0) ∧ Tendsto ε₂ atTop (𝓝 0) ∧ 0 < K ∧
      ∀ N T R Mb W : ℕ, 0 < N → 0 < T → 0 < R → 0 < Mb → 0 < W →
        T ∣ W → W ∣ Mb → Mb ∣ N → 2 * R ≤ T →
        ∃ c : ℕ → List Bool,
          (∀ r < N / T, (c r).length = T ∧ (c r).count true ≤ R ∧
            ((oddSqPrimeBlock T r).count true ≤ R → c r = oddSqPrimeBlock T r)) ∧
          RunsWithin A out
            (Encoding.encodeList id [binWord N, binWord T, binWord R, binWord Mb, binWord W])
            ((List.range (N / T)).flatMap c)
            (K * ((N : ℝ) * ((R : ℝ) * logU (T : ℝ) * logU (N : ℝ) / T) * Mul.Mstar N
              + (N : ℝ) * ((rho W : ℝ) * logU (N : ℝ) / W) * Mul.Mstar N
              + ((Mb : ℝ) + ((N / Mb : ℕ) : ℝ)) * logU (N : ℝ) ^ 3
              + (N : ℝ) * logU (W : ℝ) * Mul.Mstar W * TS.Kstar N
              + (N : ℝ) * logU ((N / Mb : ℕ) : ℝ) * RP.Rstar (N / Mb) * TS.Kstar W * TS.Kstar N
              + (1 + (R : ℝ) * logU (T : ℝ) ^ (4 + ε₁ T) / T) * N * logU (T : ℝ) *
                  Cstar Mul TS T * TS.Kstar N
              + (T : ℝ) * logU (T : ℝ) ^ (3 + ε₂ T))) := by sorry

end Supplement

end FasterPrimeEnum
