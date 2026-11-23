-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_re_inner_tsum
-- name    : Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.re_inner_tsum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:30.703378+00:00
-- url     : https://prove2.me/theorems/bb7e3954-44c3-4fa3-893b-a05a5d44a77b
-- title:
--   Growth Polynomial Operator: re inner tsum
-- statement:
--   The Growth Polynomial Operator construction uses the re inner tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L658-L660
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L658-L660

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
open Classical
variable {τ H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]

theorem Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.re_inner_tsum (f : τ → H₁) (hf : Summable f) (w : H₁) :
    (inner ℂ w (∑' t, f t)).re = ∑' t, (inner ℂ w (f t)).re := by sorry
