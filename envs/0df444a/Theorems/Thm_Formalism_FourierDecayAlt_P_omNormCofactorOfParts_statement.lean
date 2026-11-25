-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_omNormCofactorOfParts_statement
-- name    : Formalism.FourierDecayAlt.P.omNormCofactorOfParts_statement
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:36:53.070032+00:00
-- url     : https://prove2.me/theorems/484bada9-f6fa-555f-b1cd-e2e85d0eb83f
-- title:
--   P: om Norm Cofactor Of Parts statement
-- statement:
--   The P construction uses the om Norm Cofactor Of Parts statement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OmegaNormCofactorOfParts.lean#L96-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OmegaNormCofactorOfParts.lean#L96-L96

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmegaNormCofactorOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.omNormCofactorOfParts_statement : C7.OmNormCofactorOfParts := by sorry
