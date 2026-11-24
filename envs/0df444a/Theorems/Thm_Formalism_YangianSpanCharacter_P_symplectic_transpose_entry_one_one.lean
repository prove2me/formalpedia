-- Prove2me | Theorems.Thm_Formalism_YangianSpanCharacter_P_symplectic_transpose_entry_one_one
-- name    : Formalism.YangianSpanCharacter.P.symplectic_transpose_entry_one_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:39:29.130836+00:00
-- url     : https://prove2.me/theorems/45229e46-2b7b-4bcb-ba5c-421cd8fbcf69
-- title:
--   P: symplectic transpose entry one one
-- statement:
--   The P construction uses the symplectic transpose entry one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/SymplecticTransposeEntryZeroOne.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/SymplecticTransposeEntryZeroOne.lean#L24-L32

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SymplecticTransposeEntryZeroOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem Formalism.YangianSpanCharacter.P.symplectic_transpose_entry_one_one {t : 𝕜 → Matrix (Fin 2) (Fin 2) A} {q : 𝕜 → 𝕜}
    (h : ∀ Y : 𝕜, t Y * Formalism.YangianSpanCharacter.T.J A * (t (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J A) (Y : 𝕜) :
    t Y 1 1 * t (Y + 1) 1 0 = t Y 1 0 * t (Y + 1) 1 1 := by sorry
