-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_jf_cVRho_alt
-- name    : Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.jf_cVRho_alt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:13.636885+00:00
-- url     : https://prove2.me/theorems/4a1ea480-d547-4221-90a2-83e8cba3bce0
-- title:
--   Finite Sum Local Expansion: jf c VRho alt
-- statement:
--   The Finite Sum Local Expansion construction uses the jf c VRho alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L409-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L409-L409

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

theorem Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.jf_cVRho_alt : Formalism.FourierDecayAlt.JF.CVRho := by sorry
