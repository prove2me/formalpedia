-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hAt_zero_left
-- name    : Formalism.L2.FormalSeriesBounds.VP.hAt_zero_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:52:55.400808+00:00
-- url     : https://prove2.me/theorems/b46df54a-cb34-5e91-8bfe-634b04692b54
-- title:
--   VP: h At zero left
-- statement:
--   The VP construction uses the h At zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstPartialLawAtPoints.lean#L49-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstPartialLawAtPoints.lean#L49-L82

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

theorem Formalism.L2.FormalSeriesBounds.VP.hAt_zero_left {c : Fin dd → MvPowerSeries τ C} (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0) :
    hAt Y (fun _ => 0) c = 0 := by sorry
