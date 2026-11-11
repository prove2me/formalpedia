-- Prove2me | Theorems.Thm_CubicPermFPRAS_theorem_1
-- name    : CubicPermFPRAS.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:43.573748+00:00
-- url     : https://prove2.me/theorems/89653183-d88e-447a-80cf-4f5012a0cd7c
-- title:
--   Theorem 1, p.1 — an FPRAS for the permanent of 0/1 matrices in $O(n^3\varepsilon^{-2}\log^6(n/\varepsilon))$ operations (corrected: $\log^6(2n/\varepsilon)$ for $\log^6(n/\varepsilon)$)
-- statement:
--   There are constants $\mathrm{prm}$ for the algorithm and $K>0$ such that for every $n\ge1$, every $n\times n$ matrix $A$ with entries in $\{0,1\}$ and every $\varepsilon\in(0,1)$, the algorithm of the paper (with its operation cap) run on a uniform random tape
--
--   1. outputs an estimate $\hat p\ge0$ on every tape;
--   2. uses at most $K\,n^3\varepsilon^{-2}\log^6(2n/\varepsilon)$ operations on every tape;
--   3. satisfies
--   $$\Pr\big[(1-\varepsilon)\,\mathrm{per}(A)\le\hat p\le(1+\varepsilon)\,\mathrm{per}(A)\big]\ge\frac34 .$$
--
--   This is the paper's main result: an $\widetilde O(n^3)$-time FPRAS for the permanent of 0/1 matrices, improving $\widetilde O(n^6)$.
--
--   **Formalization Note** The failure event is measured with the outer product measure of the tape and has probability at most $1/4$.
--
--   Differences from the source:
--   - correction: running time $O(n^3\varepsilon^{-2}\log^6(n/\varepsilon))$ → at most $Kn^3\varepsilon^{-2}\log^6(2n/\varepsilon)$; reason: at $n=1$ and $A=(1)$, $\log(1/\varepsilon)\to0$ as $\varepsilon\to1$, so the printed bound tends to $0$, while every run performs at least one operation; for $n\ge2$, $\log(2n/\varepsilon)\le2\log(n/\varepsilon)$, so the two bounds agree up to the constant
--   - generalization: "there is a randomized algorithm" → the paper's algorithm written out as `permFPRAS`, with its constants quantified before the instance; reason: the defined algorithm witnesses the existential; quantifying constants first is the paper's "for sufficiently large $C$" (p.56)
--   - encoding: unit-cost running time; $\Pr[\cdot]\ge3/4$ → the charged cost of the run on every tape; the outer measure of the failure event is at most $1/4$; reason: the paper counts arithmetic operations and comparisons at unit cost (p.1); the failure bound implies the success bound
--   - encoding: an $n\times n$ 0/1 matrix; $\mathrm{per}(A)=\sum_\sigma\prod_ia_{i,\sigma(i)}$ → $n\ge1$, a real matrix with entries in $\{0,1\}$; `Matrix.permanent A`$=\sum_\sigma\prod_iA_{\sigma(i),i}$; reason: the paper's $V_1,V_2$ are nonempty; the permanent is invariant under transposition
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Theorem 1, p.1 (PDF 3); proof, p.56 (PDF 58)

import Mathlib
import Definitions.Def_CubicPermFPRAS_permFPRAS

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Theorem 1**, p.1 (PDF 3), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…) (corrected: `log⁶(2n/ε)` for `log⁶(n/ε)`); proved on
p.56 (PDF 58).

There is a randomized algorithm that, given an `n × n` 0/1 matrix `A` and `ε ∈ (0,1)`, outputs
an estimate `p̂ ≥ 0` such that `Pr[(1 − ε) per(A) ≤ p̂ ≤ (1 + ε) per(A)] ≥ 3/4`, and has running
time `O(n³ ε⁻² log⁶(n/ε))`, counting arithmetic operations and comparisons at unit cost.

**Formalization Note.** The algorithm is the paper's, written out as `permFPRAS` (a charged
program on a uniform random tape, with the operation cap of p.56); its "sufficiently large"
constants `prm` and the constant `K` of the `O(·)` are quantified before the instance. Output
`p̂ ≥ 0` and the time bound hold on every tape; the failure event is measured with the (outer)
product measure of the tape and has probability at most `1/4`. The time bound uses
`log(2n/ε)`: at `n = 1` the printed `log(1/ε)` tends to `0` as `ε → 1`, while every run performs
at least one operation; for `n ≥ 2`, `log(2n/ε) ≤ 2 log(n/ε)`. `A` is a real matrix with entries
in `{0,1}`, and `Matrix.permanent A = ∑_σ ∏_i A (σ i) i` equals the paper's
`∑_σ ∏_i a_{i,σ(i)}` (transpose invariance). -/
theorem theorem_1 : ∃ (prm : Params) (K : ℝ), 0 < K ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (A : Matrix (Fin n) (Fin n) ℝ), (∀ i j, A i j = 0 ∨ A i j = 1) →
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∀ ω : Tape, 0 ≤ (permFPRAS prm A ε ω).out) ∧
      (∀ ω : Tape, ((permFPRAS prm A ε ω).cost : ℝ) ≤
        K * (n : ℝ) ^ 3 * ε⁻¹ ^ 2 * Real.log (2 * n / ε) ^ 6) ∧
      tapeMeasure {ω | ¬ ((1 - ε) * A.permanent ≤ (permFPRAS prm A ε ω).out ∧
        (permFPRAS prm A ε ω).out ≤ (1 + ε) * A.permanent)} ≤ 1 / 4 := by sorry

end CubicPermFPRAS
