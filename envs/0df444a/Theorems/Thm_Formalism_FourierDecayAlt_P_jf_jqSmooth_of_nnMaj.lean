-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_jf_jqSmooth_of_nnMaj
-- name    : Formalism.FourierDecayAlt.P.jf_jqSmooth_of_nnMaj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:33:02.410003+00:00
-- url     : https://prove2.me/theorems/6acfc8d3-ddbd-5422-a25b-3d27dfdc91bd
-- title:
--   P: jf jq Smooth of nn Maj
-- statement:
--   The P construction uses the jf jq Smooth of nn Maj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfJqSmoothOfNnMaj.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfJqSmoothOfNnMaj.lean#L19-L20

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JConvOfJDom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CellSmoothness
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.jf_jqSmooth_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JqSmooth := by sorry
