-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_lam_inj
-- name    : Formalism.L2.FormalSeriesBounds.RF.lam_inj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:00:53.194382+00:00
-- url     : https://prove2.me/theorems/bce45f6c-a6b4-4907-8491-5bfb8973a297
-- title:
--   RF: lam inj
-- statement:
--   The RF construction uses the lam inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GramMatrixMulRight.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GramMatrixMulRight.lean#L27-L41

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

theorem Formalism.L2.FormalSeriesBounds.RF.lam_inj (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) :
    Function.Injective (lam r tau plc) := by sorry
