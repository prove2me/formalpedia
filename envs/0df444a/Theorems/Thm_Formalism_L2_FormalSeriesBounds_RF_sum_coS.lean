-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_sum_coS
-- name    : Formalism.L2.FormalSeriesBounds.RF.sum_coS
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:26.743532+00:00
-- url     : https://prove2.me/theorems/c61f8040-e36d-48f8-9b1e-d02026278de2
-- title:
--   RF: sum co S
-- statement:
--   The RF construction uses the sum co S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GramMatrixMulRight.lean#L87-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GramMatrixMulRight.lean#L87-L98

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

theorem Formalism.L2.FormalSeriesBounds.RF.sum_coS (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) {M : Type} [AddCommMonoid M]
    (α : AA r tau N) (col : Fin 2) (Φ : C → (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) → M) (h0 : ∀ y, Φ 0 y = 0) :
    ∑ y, Φ (coS r tau gm plc (lam r tau plc (α, col)) y) y =
      ∑ g, Φ (Mm r tau gm α col g) ((eW r tau N).symm (α, g)) := by sorry
