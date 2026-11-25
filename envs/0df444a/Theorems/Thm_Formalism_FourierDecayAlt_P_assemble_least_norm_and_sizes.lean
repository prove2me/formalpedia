-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_assemble_least_norm_and_sizes
-- name    : Formalism.FourierDecayAlt.P.assemble_least_norm_and_sizes
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:09.586286+00:00
-- url     : https://prove2.me/theorems/e91f6781-4944-5c92-a40d-cc2ccabdaae1
-- title:
--   P: assemble least norm and sizes
-- statement:
--   The P construction uses the assemble least norm and sizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationScaledIdealMemIff.lean#L598-L600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationScaledIdealMemIff.lean#L598-L600

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x2

theorem Formalism.FourierDecayAlt.P.assemble_least_norm_and_sizes : Formalism.FourierDecayAlt.S6.AssembleLeast := by sorry
