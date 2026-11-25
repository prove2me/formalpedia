-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_good_sumL
-- name    : Formalism.L2.FormalSeriesBounds.VP.good_sumL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:04.492144+00:00
-- url     : https://prove2.me/theorems/cecf72fa-f8b8-5a55-96ee-ad33dc94fe6f
-- title:
--   VP: good sum L
-- statement:
--   The VP construction uses the good sum L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstPartialLawAtPoints.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstPartialLawAtPoints.lean#L168-L170

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
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

theorem Formalism.L2.FormalSeriesBounds.VP.good_sumL : ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) → GoodPt V (sumL Y l)
  := by sorry
