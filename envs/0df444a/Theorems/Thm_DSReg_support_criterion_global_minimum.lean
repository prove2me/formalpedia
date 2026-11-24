-- Prove2me | Theorems.Thm_DSReg_support_criterion_global_minimum
-- name    : DSReg.support_criterion_global_minimum
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:28:54.082048+00:00
-- url     : https://prove2.me/theorems/d6eada7a-d11a-4311-87d5-3e493d9bfc01
-- title:
--   Remark 1: global minimum of the support criterion
-- statement:
--   Let $x=g(z)$, with $g$ differentiable $\mu$-a.e. and measurable Jacobian $D$, and assume Functional no-cancellation (Assumption 2) but not Structural Diversity. Then:
--
--   1. for every $U\in O(d)$, $\|D(\cdot)U\|_{0,\mu}\ge\sum_{i=1}^d|\mathcal S_i|$;
--   2. every signed permutation $P$ attains $\|D(\cdot)P\|_{0,\mu}=\sum_{i=1}^d|\mathcal S_i|$, so this sum is the global minimum of the support criterion;
--   3. if $\mathcal S_i=\mathcal S_j$ for some $i\ne j$, some $U\in O(d)$ that is not a signed permutation also attains $\sum_i|\mathcal S_i|$.
--
--   **Formalization Note** The remark's last sentence says that a Givens rotation in the $(i,j)$ plane gives such a $U$. The statement asserts only that a non-permutation minimizer exists, which is the conclusion the remark draws.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Appendix A.2, Remark 1, p. 19

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem support_criterion_global_minimum {d p : ℕ} (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (g : (Fin d → ℝ) → Fin p → ℝ)
    (hdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ g z) (hmeas : ∀ r i, Measurable fun z => depJac g z r i)
    (hfnc : FunctionalNoCancellation μ (depJac g)) :
    (∀ U ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      sStar μ (depJac g) ≤ supportCount μ (fun z => depJac g z * U)) ∧
    (∀ P : Matrix (Fin d) (Fin d) ℝ, IsSignedPerm P →
      supportCount μ (fun z => depJac g z * P) = sStar μ (depJac g)) ∧
    (∀ i j : Fin d, i ≠ j → footprint μ (depJac g) i = footprint μ (depJac g) j →
      ∃ U ∈ Matrix.orthogonalGroup (Fin d) ℝ, ¬ IsSignedPerm U ∧
        supportCount μ (fun z => depJac g z * U) = sStar μ (depJac g)) := by sorry

end DSReg
