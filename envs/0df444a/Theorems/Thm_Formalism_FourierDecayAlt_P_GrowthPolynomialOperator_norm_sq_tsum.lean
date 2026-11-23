-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_norm_sq_tsum
-- name    : Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.norm_sq_tsum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:19.054398+00:00
-- url     : https://prove2.me/theorems/c9cd94d8-d26c-4da0-aa7c-d90b9427a829
-- title:
--   Growth Polynomial Operator: norm sq tsum
-- statement:
--   The Growth Polynomial Operator construction uses the norm sq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L674-L691
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L674-L691

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

theorem Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.norm_sq_tsum [CompleteSpace H₁] (f : τ → H₁) (hf : Summable (fun t => ‖f t‖)) :
    ‖∑' t, f t‖ ^ 2 = ∑' p : τ × τ, (inner ℂ (f p.1) (f p.2)).re := by sorry
