-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_coS_lam
-- name    : Formalism.L2.FormalSeriesBounds.RF.coS_lam
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:02:13.604074+00:00
-- url     : https://prove2.me/theorems/b0fca1fa-78ae-4cb7-8773-5fc664803f62
-- title:
--   RF: co S lam
-- statement:
--   The RF construction uses the co S lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GramMatrixMulRight.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GramMatrixMulRight.lean#L77-L85

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
variable (r tau gm)
variable {r tau gm}

theorem Formalism.L2.FormalSeriesBounds.RF.coS_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α α' : AA r tau N) (col g : Fin 2) :
    coS r tau gm plc (lam r tau plc (α, col)) ((eW r tau N).symm (α', g)) = if α = α' then Mm r tau gm α col g else 0 := by sorry
