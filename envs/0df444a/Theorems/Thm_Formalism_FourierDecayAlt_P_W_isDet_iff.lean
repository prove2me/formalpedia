-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_W_isDet_iff
-- name    : Formalism.FourierDecayAlt.P.W.isDet_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:29.448015+00:00
-- url     : https://prove2.me/theorems/4af4231b-dedc-4ecc-a806-4479c7504e06
-- title:
--   W: is Det iff
-- statement:
--   The W construction uses the is Det iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L47-L51

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

theorem Formalism.FourierDecayAlt.P.W.isDet_iff (M : R → Matrix (Fin 2) (Fin 2) B) (q : R → R) :
    IsDet M q ↔ ∀ Y : R, (M (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J B * M Y = q Y • Formalism.YangianSpanCharacter.T.J B ∧
      M Y * Formalism.YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J B := by sorry
