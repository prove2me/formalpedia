-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_W_transpose_mul_of_comm
-- name    : Formalism.FourierDecayAlt.P.W.transpose_mul_of_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:34.248783+00:00
-- url     : https://prove2.me/theorems/0e34d69c-c5d2-4a9f-9e39-472851314472
-- title:
--   W: transpose mul of comm
-- statement:
--   The W construction uses the transpose mul of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L42-L45

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

theorem Formalism.FourierDecayAlt.P.W.transpose_mul_of_comm (A C : Matrix (Fin 2) (Fin 2) B)
    (h : ∀ i j k l, A i j * C k l = C k l * A i j) : (A * C)ᵀ = Cᵀ * Aᵀ := by sorry
