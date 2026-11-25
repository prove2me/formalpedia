-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_gram_matrix_mul_left
-- name    : Formalism.L2.FormalSeriesBounds.RF.gram_matrix_mul_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:46.851409+00:00
-- url     : https://prove2.me/theorems/46398348-6da6-4ece-a6f6-9950e5c7e824
-- title:
--   RF: gram matrix mul left
-- statement:
--   The RF construction uses the gram matrix mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GramMatrixMulRight.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GramMatrixMulRight.lean#L59-L68

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] (r : T → ℕ) (tau : Orb → ZMod 2 → T)
  (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
variable {r tau}
variable (r tau)
variable {r tau gm}

theorem Formalism.L2.FormalSeriesBounds.RF.gram_matrix_mul_left (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (col col' : Fin 2) : ∑ g, Gm r tau gm α col' g * Mm r tau gm α col g = if col' = col then 1 else 0 := by sorry
