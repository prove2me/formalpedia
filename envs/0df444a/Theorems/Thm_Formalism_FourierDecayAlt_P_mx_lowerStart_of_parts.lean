-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_mx_lowerStart_of_parts
-- name    : Formalism.FourierDecayAlt.P.mx_lowerStart_of_parts
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:34:05.016322+00:00
-- url     : https://prove2.me/theorems/512cd726-18a5-51aa-9e0d-165cd707c723
-- title:
--   P: mx lower Start of parts
-- statement:
--   The P construction uses the mx lower Start of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GammaFamilyCommuteGenerators.lean#L653-L655
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GammaFamilyCommuteGenerators.lean#L653-L655

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.mx_lowerStart_of_parts (hH : Formalism.FourierDecayAlt.M.QQHerm) (hR : Formalism.FourierDecayAlt.M.QQRTT) (hD : Formalism.FourierDecayAlt.M.QQDet) :
    Formalism.FourierDecayAlt.M.LowerStart := by sorry
