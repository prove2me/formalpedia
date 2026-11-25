-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_biadd_left
-- name    : Formalism.L2.FormalSeriesBounds.VP.biadd_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:52:43.303993+00:00
-- url     : https://prove2.me/theorems/9f055553-67b4-55ca-b189-ebbe4cd1503d
-- title:
--   VP: biadd left
-- statement:
--   The VP construction uses the biadd left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstPartialLawAtPoints.lean#L204-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstPartialLawAtPoints.lean#L204-L227

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
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

theorem Formalism.L2.FormalSeriesBounds.VP.biadd_left {c : Fin dd → MvPowerSeries τ C} (hc : GoodPt V c) :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ mvExp (hAt Y (sumL Y l) c) * U = (l.map fun a => mvExp (hAt Y a c)).prod
  := by sorry
