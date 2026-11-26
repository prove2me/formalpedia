-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_ball_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:21.944179+00:00
-- url     : https://prove2.me/submissions/29d07874-0bdc-452d-9ae1-fee0119031c4

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_of_resolvent_shift
import Theorems.Thm_resolvent_sub_smul_one_shift


set_option autoImplicit false
open Complex MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) p =
      crouzeixPolynomialAuxiliaryOperator
        (A - c • (1 : E →L[ℂ] E)) (SmoothJordanDomain.ball 0 R hR)
          (p.affineComposition 1 c) :=
  crouzeixPolynomialAuxiliaryOperator_ball_center_of_resolvent_shift
    A c hR p (resolvent_sub_smul_one_shift A c)
