-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_actAt_sumL
-- name    : Formalism.L2.FormalSeriesBounds.VP.actAt_sumL
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:12.141166+00:00
-- url     : https://prove2.me/theorems/d39fae94-7d9d-5d1c-93c7-116b9f44087d
-- title:
--   VP: act At sum L
-- statement:
--   The VP construction uses the act At sum L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L72-L79

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
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

theorem Formalism.L2.FormalSeriesBounds.VP.actAt_sumL (x : O) : ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
    actAt Y x (sumL Y l) = sumL Y (l.map (actAt Y x))
  := by sorry
