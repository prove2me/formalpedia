-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_le_cutoff_limit_in_L2
-- name    : Formalism.FourierDecayAlt.P.le_cutoff_limit_in_L2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:32:26.037798+00:00
-- url     : https://prove2.me/theorems/39e0e8a6-af79-56fb-a92b-ac9f65692c75
-- title:
--   P: le cutoff limit in L2
-- statement:
--   The P construction uses the le cutoff limit in L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivedCoefficientIntegrable.lean#L442-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivedCoefficientIntegrable.lean#L442-L443

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem Formalism.FourierDecayAlt.P.le_cutoff_limit_in_L2 : Formalism.FourierDecayAlt.LE.CutoffLimitInL2 := by sorry
