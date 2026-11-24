-- Prove2me | Theorems.Thm_DSReg_functional_support_minimality
-- name    : DSReg.functional_support_minimality
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:28:23.611792+00:00
-- url     : https://prove2.me/theorems/dc2e57b6-4e78-41f3-9e41-7aae23625d5f
-- title:
--   Lemma 3: functional support minimality
-- statement:
--   Let $x=g(z)$, with $g$ differentiable $\mu$-a.e. and measurable Jacobian $D$, and assume Structural Diversity (Assumption 1) and Functional no-cancellation (Assumption 2). If $U\in O(d)$ solves
--
--   $$\min_{U\in O(d)}\|D(\cdot)U\|_{0,\mu},$$
--
--   then $U$ is a signed permutation matrix.
--
--   **Formalization Note** "Under the assumptions of Theorem 2" is taken to mean the assumptions on $g$, $D$ and $\mu$. The premise $h(z)=Qz$ does not enter this matrix problem and is omitted.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Appendix A.2, Lemma 3, pp. 17-19

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem functional_support_minimality {d p : ℕ} (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (g : (Fin d → ℝ) → Fin p → ℝ)
    (hdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ g z) (hmeas : ∀ r i, Measurable fun z => depJac g z r i)
    (hsd : StructuralDiversity (footprint μ (depJac g)))
    (hfnc : FunctionalNoCancellation μ (depJac g))
    (U : Matrix (Fin d) (Fin d) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hmin : ∀ U' ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      supportCount μ (fun z => depJac g z * U) ≤ supportCount μ (fun z => depJac g z * U')) :
    IsSignedPerm U := by sorry

end DSReg
