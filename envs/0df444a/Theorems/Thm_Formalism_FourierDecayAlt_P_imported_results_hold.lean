-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_imported_results_hold
-- name    : Formalism.FourierDecayAlt.P.imported_results_hold
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:27.515836+00:00
-- url     : https://prove2.me/theorems/1643d7d8-88d0-4912-a3ab-f40eb5b1da0e
-- title:
--   P: imported results hold
-- statement:
--   The P construction uses the imported results hold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivedCoefficientIntegrable.lean#L496-L535
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivedCoefficientIntegrable.lean#L496-L535

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

theorem Formalism.FourierDecayAlt.P.imported_results_hold : Formalism.FourierDecayAlt.LE.PImportsHold := by sorry
