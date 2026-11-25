-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hRow_eq
-- name    : Formalism.L2.FormalSeriesBounds.VP.hRow_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:46:59.589129+00:00
-- url     : https://prove2.me/theorems/89a623a0-48b8-4f3c-bf98-e09360246494
-- title:
--   VP: h Row eq
-- statement:
--   The VP construction uses the h Row eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfBiadditiveCross.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfBiadditiveCross.lean#L24-L30

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
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
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP

theorem Formalism.L2.FormalSeriesBounds.VP.hRow_eq (Y : FBChart C V O dd) {J : Fin 2 → Type} [∀ g, Fintype (J g)] (q : PairData Y d J) :
    (Y.raw q).hRow = (Y.k : C) • hAt Y ((Y.raw q).expPt 0) ((Y.raw q).expPt 1) := by sorry
