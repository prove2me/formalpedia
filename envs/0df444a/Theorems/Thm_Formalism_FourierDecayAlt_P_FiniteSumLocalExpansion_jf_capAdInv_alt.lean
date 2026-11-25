-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_jf_capAdInv_alt
-- name    : Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.jf_capAdInv_alt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:26:57.163246+00:00
-- url     : https://prove2.me/theorems/6a58a832-1ddb-54b0-9e61-b49d518d3f13
-- title:
--   Finite Sum Local Expansion: jf cap Ad Inv alt
-- statement:
--   The Finite Sum Local Expansion construction uses the jf cap Ad Inv alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L405-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L405-L405

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section

theorem Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.jf_capAdInv_alt : Formalism.FourierDecayAlt.P.JFxB.CapAdInv := by sorry
