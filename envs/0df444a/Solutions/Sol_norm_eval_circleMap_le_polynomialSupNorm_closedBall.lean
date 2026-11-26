-- Prove2me | solution 1 for norm_eval_circleMap_le_polynomialSupNorm_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:56.842597+00:00
-- url     : https://prove2.me/submissions/2b9f3318-a861-4220-b684-3a18cee5b082

import Definitions.Def_Operator_Crouzeix_CircleKernel
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (p : ℂ[X]) (c : ℂ) {R : ℝ}
    (hR : 0 ≤ R) (t : ℝ) :
    ‖p.eval (circleMap c R t)‖ ≤ polynomialSupNorm p (Metric.closedBall c R) :=
  norm_eval_le_polynomialSupNorm p
    (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
    (circleMap_mem_closedBall c hR t)
