-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_ex_add
-- name    : Formalism.L2.FormalSeriesBounds.VP.ex_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:09.327273+00:00
-- url     : https://prove2.me/theorems/0dc1c08d-e6b9-45db-9f8f-66f08762ee3e
-- title:
--   VP: ex add
-- statement:
--   The VP construction uses the ex add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L61-L71

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValueEquationOfProjectors
import Theorems.Thm_Formalism_L2_Pj_ex_add

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
variable (Y : FBChart C V O dd)

theorem Formalism.L2.FormalSeriesBounds.VP.ex_add {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    exAt Y (fun m => a m + b m) = addAt Y (exAt Y a) (exAt Y b) := by sorry
