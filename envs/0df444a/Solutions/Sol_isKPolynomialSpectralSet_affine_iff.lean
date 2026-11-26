-- Prove2me | solution 1 for isKPolynomialSpectralSet_affine_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:59.57689+00:00
-- url     : https://prove2.me/submissions/57e8e436-f589-49a7-97ce-0be20752990a

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
import Theorems.Thm_IsKPolynomialSpectralSet_affine
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition



set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsKPolynomialSpectralSet (a • A + b • 1) K
        ((fun z => a * z + b) '' X) ↔
      IsKPolynomialSpectralSet A K X := by
  constructor
  · intro h
    have hinv := h.affine (inv_ne_zero ha) (-a⁻¹ * b)
    have hop :
        a⁻¹ • (a • A + b • 1) + (-a⁻¹ * b) • 1 = A := by
      simp only [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul]
      module
    have hset :
        (fun z => a⁻¹ * z + -a⁻¹ * b) ''
            ((fun z => a * z + b) '' X) = X := by
      ext z
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        convert hw using 1
        field_simp [ha]
        ring
      · intro hz
        refine ⟨a * z + b, ⟨z, hz, rfl⟩, ?_⟩
        field_simp [ha]
        ring
    rw [hop, hset] at hinv
    exact hinv
  · exact fun h => h.affine ha b
