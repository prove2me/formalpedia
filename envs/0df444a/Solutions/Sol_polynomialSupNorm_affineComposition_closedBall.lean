-- Prove2me | solution 1 for polynomialSupNorm_affineComposition_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:47.84864+00:00
-- url     : https://prove2.me/submissions/cfbf86c8-8fd7-4d39-8871-73d31b743234

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_AffineDisk
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_affineComposition_image
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace Pointwise Polynomial
theorem _root_.solution
    (p : ℂ[X]) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    polynomialSupNorm (p.affineComposition (R : ℂ) c)
        (Metric.closedBall (0 : ℂ) 1) =
      polynomialSupNorm p (Metric.closedBall c R) := by
  rw [polynomialSupNorm_affineComposition_image]
  congr 1
  have h := affinity_unitClosedBall hR c
  rw [← Set.image_vadd, ← Set.image_smul, Set.image_image] at h
  simpa only [add_comm, Complex.real_smul, vadd_eq_add] using h
