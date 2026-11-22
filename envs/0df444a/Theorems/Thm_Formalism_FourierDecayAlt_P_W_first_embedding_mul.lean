-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_W_first_embedding_mul
-- name    : Formalism.FourierDecayAlt.P.W.first_embedding_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:35.555075+00:00
-- url     : https://prove2.me/theorems/06d401bb-d2fa-43c9-9568-10da726e6ae8
-- title:
--   W: first embedding mul
-- statement:
--   The W construction uses the first embedding mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L11-L15

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.W
open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W
variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]

theorem Formalism.FourierDecayAlt.P.W.first_embedding_mul (M N : Matrix (Fin 2) (Fin 2) B) : E1 (M * N) = E1 M * E1 N := by sorry
