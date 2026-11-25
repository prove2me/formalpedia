-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pullback_two_var_one
-- name    : Formalism.L2.FormalSeriesBounds.VP.pullback_two_var_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:26.670427+00:00
-- url     : https://prove2.me/theorems/9499da51-619f-42a9-bb56-8c595b8133c3
-- title:
--   VP: pullback two var one
-- statement:
--   The VP construction uses the pullback two var one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqSelfOfUnitGerm.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqSelfOfUnitGerm.lean#L32-L34

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
open Formalism.L2.FormalSeriesBounds.VP
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem Formalism.L2.FormalSeriesBounds.VP.pullback_two_var_one : pull2 Y p (1 : PS C 2 dd) = 1 := by sorry
