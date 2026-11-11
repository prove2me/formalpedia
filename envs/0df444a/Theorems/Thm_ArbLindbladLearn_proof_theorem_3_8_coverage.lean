-- Prove2me | Theorems.Thm_ArbLindbladLearn_proof_theorem_3_8_coverage
-- name    : ArbLindbladLearn.proof_theorem_3_8_coverage
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:21:37.721527+00:00
-- url     : https://prove2.me/theorems/9a69ba69-500f-47ba-8448-93aa997be726
-- title:
--   Proof of Theorem 3.8 (p.24) — $N_{\mathrm{supp}}$ shots see every $\alpha$-heavy marginal label w.p. $1-\delta$
-- statement:
--   Let $\mu_X$ and $\mu_Z$ be probability distributions on finite sets, $\alpha>0$, $\delta\in(0,1)$ and
--   $$N_{\mathrm{supp}}=\Big\lceil\alpha^{-1}\log\frac{2}{\alpha\delta}\Big\rceil .$$
--   Draw $N_{\mathrm{supp}}$ independent samples from $\mu_X$ (their set of values is $\hat X$) and $N_{\mathrm{supp}}$ independent samples from $\mu_Z$ (values $\hat Z$). Then with probability at least $1-\delta$, every $x$ with $\mu_X(x)\ge\alpha$ lies in $\hat X$ and every $z$ with $\mu_Z(z)\ge\alpha$ lies in $\hat Z$.
--
--   This is the sampling guarantee of Algorithm 1 (line 3), which makes the candidate supports contain every heavy label.
--
--   Differences from the source:
--   - generalization: μ_X, μ_Z the marginals of μ on {0,1}ⁿ → any probability vectors on finite sets; reason: the argument uses only that they are probability distributions; the marginals are an instance
--   - encoding: probability over the two batches of shots → explicit sum over all outcome sequences of the product of the draw probabilities; reason: finite i.i.d. sampling; same probability
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), proof of Theorem 3.8, p.24; Algorithm 1 line 3, p.23

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace ArbLindbladLearn

open Classical in
/-- Proof of Theorem 3.8, coverage (Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.24; Algorithm 1, line 3,
p.23). Since `μ_X` and `μ_Z` are probability distributions, each has at most `1/α` labels of mass at
least `α`. A fixed such label is missed by all `N_supp = ⌈α⁻¹ log(2/(αδ))⌉` shots in the
corresponding batch with probability at most `(1 − α)^{N_supp} ≤ e^{−αN_supp} ≤ αδ/2`. A union bound
over the at most `2/α` heavy labels across the two marginal distributions shows that, with
probability at least `1 − δ`, every `x` with `μ_X(x) ≥ α` lies in `X̂` and every `z` with
`μ_Z(z) ≥ α` lies in `Ẑ`.

**Formalization Note** `μ_X`, `μ_Z` are any probability vectors on finite sets (in Algorithm 1,
the marginals of `μ` on `{0,1}ⁿ`), `α > 0` and `δ ∈ (0,1)` (Theorem 3.8). The two batches are
`N_supp` independent draws from each law, `X̂` and `Ẑ` their sets of values; the probability of the
event is the explicit sum over all outcome sequences of the product of the draw probabilities. -/
theorem proof_theorem_3_8_coverage {X Z : Type*} [Fintype X] [Fintype Z]
    (μX : X → ℝ) (μZ : Z → ℝ) (hX0 : ∀ x, 0 ≤ μX x) (hX1 : ∑ x, μX x = 1)
    (hZ0 : ∀ z, 0 ≤ μZ z) (hZ1 : ∑ z, μZ z = 1) (α δ : ℝ) (hα : 0 < α) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    1 - δ ≤
      ∑ xs : Fin ⌈α⁻¹ * Real.log (2 / (α * δ))⌉₊ → X,
        ∑ zs : Fin ⌈α⁻¹ * Real.log (2 / (α * δ))⌉₊ → Z,
          (∏ i, μX (xs i)) * (∏ i, μZ (zs i)) *
            (if (∀ x, α ≤ μX x → ∃ i, xs i = x) ∧ (∀ z, α ≤ μZ z → ∃ i, zs i = z)
              then 1 else 0) := by sorry

end ArbLindbladLearn
