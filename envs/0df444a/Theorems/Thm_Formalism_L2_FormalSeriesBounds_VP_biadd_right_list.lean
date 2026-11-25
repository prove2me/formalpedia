-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_biadd_right_list
-- name    : Formalism.L2.FormalSeriesBounds.VP.biadd_right_list
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:01.786254+00:00
-- url     : https://prove2.me/theorems/ac276958-87f2-5343-a2fd-4564d2e643bc
-- title:
--   VP: biadd right list
-- statement:
--   The VP construction uses the biadd right list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L81-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L81-L91

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_IsIU_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)

theorem Formalism.L2.FormalSeriesBounds.VP.biadd_right_list (l2 : List (Fin dd → MvPowerSeries τ C)) (h2 : ∀ a ∈ l2, GoodPt V a) :
    ∀ l1 : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l1, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ (l1.map fun a => mvExp (hAt Y a (sumL Y l2))).prod * U =
        (l1.map fun a => (l2.map fun b => mvExp (hAt Y a b)).prod).prod
  := by sorry
