-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteObservationMarkov_event_card_vectors
-- name    : CountingMatroid.Analysis.FiniteObservationMarkov.event_card_vectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:04:59.751322+00:00
-- url     : https://prove2.me/theorems/4dbfcebd-3f21-4c77-adc6-80b0613caf56
-- title:
--   Boolean list-event counts equal fixed-length vector-event counts
-- statement:
--   Let $t\in\mathbb N$ and let $E$ be any predicate on finite Boolean lists. Then
--
--   $$\bigl|\{b:|b|=t,\ E(b)\}\bigr|=\bigl|\{v\in\{0,1\}^t:E(\operatorname{list}(v))\}\bigr|.$$
--
--   This permits a finite-tape event to move between length-constrained lists and fixed-length vectors without changing its cardinality.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteObservationMarkov.lean#L47-L70

import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteObservationMarkov

open CountingMatroid.Analysis.RelativeObservationBounds

theorem CountingMatroid.Analysis.FiniteObservationMarkov.event_card_vectors (t : ℕ) (bad : List Bool → Prop) :
    letI := Classical.propDecidable
    Set.ncard {bits : List Bool | bits.length = t ∧ bad bits} =
      (Finset.univ.filter (fun bits : List.Vector Bool t => bad bits.val)).card := by sorry
