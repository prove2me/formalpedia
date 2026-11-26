-- Prove2me | solution 1 for spectrum_smul_add_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:45.851454+00:00
-- url     : https://prove2.me/submissions/445bb9e7-0a05-4e2c-b1d3-6ee42f9443c3

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition



set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    spectrum ℂ (a • A + b • 1) =
      (fun z => a * z + b) '' spectrum ℂ A := by
  calc
    spectrum ℂ (a • A + b • 1) =
        spectrum ℂ (a • A) + {b} := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (spectrum.add_singleton_eq (a • A) b).symm
    _ = a • spectrum ℂ A + {b} := by
      have hsmul := spectrum.unit_smul_eq_smul A (Units.mk0 a ha)
      simpa only [Units.smul_def, Units.val_mk0] using
        congrArg (· + {b}) hsmul
    _ = (fun z => a * z + b) '' spectrum ℂ A := by
      ext z
      simp only [Set.mem_add, Set.mem_smul_set, Set.mem_singleton_iff,
        Set.mem_image]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, _, rfl, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨a * w, ⟨w, hw, rfl⟩, b, rfl, rfl⟩
