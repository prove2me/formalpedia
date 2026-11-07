-- Prove2me | Theorems.Thm_ContinualCounting_theorem_1_approx_dp_lower_bound
-- name    : ContinualCounting.theorem_1_approx_dp_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:46.888603+00:00
-- url     : https://prove2.me/theorems/3380898e-d188-4887-8762-4a7ee240ba53
-- title:
--   Theorem 1 — every $(\varepsilon,\delta)$-DP mechanism for prefix sums has $\ell_\infty$ error $\Omega(\log^{3/2}n/\max\{\varepsilon,\delta\})$
-- statement:
--   Let $A$ be the $n\times n$ prefix-sum matrix. There is an absolute constant $C>0$ such that for every $\kappa>0$ there are $c>0$ and $N$ with the following property. For all $n\ge N$, all $\varepsilon$ with $n^{-1+\kappa}<\varepsilon<1$, all $0<\delta<C$, and every $(\varepsilon,\delta)$-DP mechanism $M$ on $\{0,1\}^n$ with outputs in $\mathbb R^n$,
--   $$\max_{x\in\{0,1\}^n}\mathbb E\big[\|M(x)-Ax\|_\infty\big]\ge\frac{c\,\log^{3/2}n}{\max\{\varepsilon,\delta\}}.$$
--
--   For fixed $\varepsilon$ and sufficiently small fixed $\delta>0$ this matches the dependence on $n$ of the Gaussian binary tree mechanism.
--
--   Differences from the source:
--   - reading: "For any n^{−1+Ω(1)} < ε < 1, 0 < δ < C for a sufficiently small constant C > 0 … = Ω(·)" → ∃ C > 0, ∀ κ > 0, ∃ c > 0, ∃ N, ∀ n ≥ N, ∀ ε ∈ (n^{−1+κ}, 1), ∀ δ ∈ (0, C); reason: the standard meaning: C is absolute, while c and N depend only on κ, through m = n^{Ω(1)} in the proof
--   - generalization: "any (ε, δ)-DP mechanism M for continual counting" → every (offline) mechanism {0,1}^n → probability laws on ℝ^n; reason: online mechanisms are a special case, and the paper states the bound in the offline model (p.3)
--   - encoding: log, max over x, expectation of the sup norm → `Real.log` (natural), `⨆`, `lintegral` of `enorm` in ℝ≥0∞; reason: the base of the logarithm only moves c; the error may be ∞
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Theorem 1, p.2 (PDF p.3), restated p.17 (PDF p.18)

import Mathlib
import Definitions.Def_ContinualCounting_IsDP
import Definitions.Def_ContinualCounting_linfError

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Theorem 1.** Bairaktari, Dahl, Larsen, *The Binary Tree Mechanism is Optimal for Differentially
Private Continual Counting*, arXiv:2607.00876 (sha256 986e6426…), p.2, restated p.17: "For any
n^{−1+Ω(1)} < ε < 1, 0 < δ < C for a sufficiently small constant C > 0, it holds that any (ε, δ)-DP
mechanism M for continual counting has error max_{x∈{0,1}^n} E[∥M(x) − Ax∥∞] = Ω(log^{3/2} n / max{ε, δ}),
where A is the n × n prefix-sum matrix."

**Formalization Note.** The asymptotics read: one absolute `C`; for each `κ > 0` (the `Ω(1)` of the
exponent) constants `c > 0`, `N` depending only on `κ`; and every `n ≥ N`, `n^{−1+κ} < ε < 1`, `0 < δ < C`. The
mechanism is arbitrary (data-dependent noise, the whole input visible, the offline model of p.3), which
contains the online ones. Mechanisms are probability laws on `ℝ^n`. The logarithm is natural. -/
theorem theorem_1_approx_dp_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ ε δ : ℝ, (n : ℝ) ^ (-1 + κ) < ε → ε < 1 → 0 < δ → δ < C →
      ∀ M : (Fin n → Bool) → Measure (Fin n → ℝ), (∀ x, IsProbabilityMeasure (M x)) →
        IsDP M ε δ →
        ENNReal.ofReal (c * Real.log n ^ ((3 : ℝ) / 2) / max ε δ) ≤ linfError M := by sorry

end ContinualCounting
