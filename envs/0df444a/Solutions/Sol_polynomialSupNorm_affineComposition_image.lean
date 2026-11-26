-- Prove2me | solution 1 for polynomialSupNorm_affineComposition_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:01.145816+00:00
-- url     : https://prove2.me/submissions/74c8a1b5-d7ff-417e-a9c4-7608f033a486

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_Polynomial_aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] Polynomial.aeval_affineComposition

set_option autoImplicit false
open scoped Polynomial
theorem _root_.solution (p : ℂ[X]) (a b : ℂ) (X : Set ℂ) :
    polynomialSupNorm (p.affineComposition a b) X =
      polynomialSupNorm p ((fun z : ℂ => a * z + b) '' X) := by
  simp only [polynomialSupNorm, Polynomial.eval_affineComposition]
  let f : ℂ → ℂ := fun z => a * z + b
  let g : ℂ → ℝ := fun z => ‖p.eval z‖
  change (⨆ z ∈ X, g (f z)) = ⨆ z ∈ f '' X, g z
  by_cases hB : BddAbove (Set.range fun z : X => g (f z))
  · exact (ciSup_image hB (by
      simpa only [Real.sSup_empty] using
        Real.iSup_nonneg fun z : X => norm_nonneg (p.eval (f z)))).symm
  · have hB' : ¬BddAbove (Set.range fun z : f '' X => g z) := by
      intro h
      apply hB
      simpa only [bddAbove_def, Set.mem_range, Subtype.exists, exists_prop,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Set.mem_image,
        exists_exists_and_eq_and] using h
    rw [cbiSup_of_not_bddAbove hB, cbiSup_of_not_bddAbove hB']
