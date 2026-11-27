-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_pderiv_subG_off
-- name    : Formalism.L2.FormalSeriesBounds.RF.pderiv_subG_off
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:49:18.477324+00:00
-- url     : https://prove2.me/theorems/ca4a698b-408f-4d01-9fbb-66f27e54c2d1
-- title:
--   RF: pderiv sub G off
-- statement:
--   The RF construction uses the pderiv sub G off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PderivSubGOff.lean#L39-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PderivSubGOff.lean#L39-L54

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCDeg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
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
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem Formalism.L2.FormalSeriesBounds.RF.pderiv_subG_off {p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ∀ z, ℓ ≠ lam r tau plc z) : pderiv ℓ (subG r tau gm plc p) = 0 := by sorry
