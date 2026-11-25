-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pullback_two_var_mul
-- name    : Formalism.L2.FormalSeriesBounds.VP.pullback_two_var_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:43.736667+00:00
-- url     : https://prove2.me/theorems/039813f1-c32b-5354-a383-6a8fd13d1438
-- title:
--   VP: pullback two var mul
-- statement:
--   The VP construction uses the pullback two var mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqSelfOfUnitGerm.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqSelfOfUnitGerm.lean#L23-L25

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

theorem Formalism.L2.FormalSeriesBounds.VP.pullback_two_var_mul (F G : PS C 2 dd) : pull2 Y p (F * G) = pull2 Y p F * pull2 Y p G := by sorry
