-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_coordinateChange_comp1_intertwines_action
-- name    : Formalism.L2.FormalSeriesBounds.VP.coordinateChange_comp1_intertwines_action
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:16.564722+00:00
-- url     : https://prove2.me/theorems/fc1c179a-a0c5-5308-a8bd-c38f18896432
-- title:
--   VP: coordinate Change comp1 intertwines action
-- statement:
--   The VP construction uses the coordinate Change comp1 intertwines action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L18-L26

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_GoodPt_act

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

theorem Formalism.L2.FormalSeriesBounds.VP.coordinateChange_comp1_intertwines_action {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.A.act x) a = actAt Y x a := by sorry
