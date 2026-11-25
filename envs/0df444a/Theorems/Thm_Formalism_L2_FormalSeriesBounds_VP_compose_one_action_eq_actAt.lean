-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_compose_one_action_eq_actAt
-- name    : Formalism.L2.FormalSeriesBounds.VP.compose_one_action_eq_actAt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:50.606353+00:00
-- url     : https://prove2.me/theorems/492cd883-b58b-54f4-bbe9-78ca0b467309
-- title:
--   VP: compose one action eq act At
-- statement:
--   The VP construction uses the compose one action eq act At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffTripleSubstitution.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffTripleSubstitution.lean#L102-L104

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
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

theorem Formalism.L2.FormalSeriesBounds.VP.compose_one_action_eq_actAt {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.actK C x) a = actAt Y x a := by sorry
