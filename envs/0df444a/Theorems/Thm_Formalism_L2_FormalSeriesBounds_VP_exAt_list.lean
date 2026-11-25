-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_exAt_list
-- name    : Formalism.L2.FormalSeriesBounds.VP.exAt_list
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:58.659081+00:00
-- url     : https://prove2.me/theorems/f81650ed-2192-4b85-9b7a-5c2b32a2f235
-- title:
--   VP: ex At list
-- statement:
--   The VP construction uses the ex At list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L89-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L89-L103

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValueEquationOfProjectors
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

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

theorem Formalism.L2.FormalSeriesBounds.VP.exAt_list : ∀ L : List (Fin dd → MvPowerSeries τ C),
    (∀ a ∈ L, ∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
    exAt Y (fun m => (L.map fun a => a m).sum) = sumL Y (L.map (exAt Y))
  := by sorry
