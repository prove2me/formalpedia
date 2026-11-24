-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_SS_mem
-- name    : Formalism.FourierDecayAlt.P.Mx8.SS_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:47:18.769975+00:00
-- url     : https://prove2.me/theorems/85bdbaa6-a327-48b9-8bad-02b574bd1351
-- title:
--   Mx8: SS mem
-- statement:
--   The Mx8 construction uses the SS mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GammaFamilyCommuteGenerators.lean#L437-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GammaFamilyCommuteGenerators.lean#L437-L441

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx8

theorem Formalism.FourierDecayAlt.P.Mx8.SS_mem (P : Par) (i : Fin P.r) (l : ℕ) : SS P l ∈ Cen P i := by sorry
