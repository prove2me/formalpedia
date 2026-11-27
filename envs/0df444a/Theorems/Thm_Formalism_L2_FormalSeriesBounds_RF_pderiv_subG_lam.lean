-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_pderiv_subG_lam
-- name    : Formalism.L2.FormalSeriesBounds.RF.pderiv_subG_lam
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:47:43.729315+00:00
-- url     : https://prove2.me/theorems/b7e785b8-ba50-4418-a85c-c13f691c279c
-- title:
--   RF: pderiv sub G lam
-- statement:
--   The RF construction uses the pderiv sub G lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PderivSubGOff.lean#L91-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PderivSubGOff.lean#L91-L108

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

theorem Formalism.L2.FormalSeriesBounds.RF.pderiv_subG_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α0 : AA r tau N) (col0 : Fin 2)
    (p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc p) =
      ∑ g, MvPolynomial.C (Gm r tau gm α0 col0 g) * subG r tau gm plc (pderiv ((eW r tau N).symm (α0, g)) p) := by sorry
