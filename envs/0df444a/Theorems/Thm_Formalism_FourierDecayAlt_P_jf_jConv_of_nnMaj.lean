-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_jf_jConv_of_nnMaj
-- name    : Formalism.FourierDecayAlt.P.jf_jConv_of_nnMaj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:35:01.706798+00:00
-- url     : https://prove2.me/theorems/fe5a6bfc-9ab7-48c5-820d-c30255039d2f
-- title:
--   P: jf j Conv of nn Maj
-- statement:
--   The P construction uses the jf j Conv of nn Maj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfJqSmoothOfNnMaj.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfJqSmoothOfNnMaj.lean#L13-L14

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

theorem Formalism.FourierDecayAlt.P.jf_jConv_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JConv := by sorry
