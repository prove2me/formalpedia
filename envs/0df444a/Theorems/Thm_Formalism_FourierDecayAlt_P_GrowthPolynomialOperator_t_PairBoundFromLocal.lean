-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_t_PairBoundFromLocal
-- name    : Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_PairBoundFromLocal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:49.186876+00:00
-- url     : https://prove2.me/theorems/4f607c59-79d3-4841-b35f-c788b92ac6dd
-- title:
--   Growth Polynomial Operator: t Pair Bound From Local
-- statement:
--   The Growth Polynomial Operator construction uses the t Pair Bound From Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L1236-L1267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L1236-L1267

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
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB Finset NumberField

theorem Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_PairBoundFromLocal : PairBoundFromLocal := by sorry
