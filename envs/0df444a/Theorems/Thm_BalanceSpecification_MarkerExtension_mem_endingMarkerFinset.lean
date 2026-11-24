-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_mem_endingMarkerFinset
-- name    : BalanceSpecification.MarkerExtension.mem_endingMarkerFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:39.697643+00:00
-- url     : https://prove2.me/theorems/f76d19d8-2b0d-4234-aab8-3fff25b58984
-- title:
--   Marker Extension: mem ending Marker Finset
-- statement:
--   The Marker Extension construction uses the mem ending Marker Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L25-L28
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L25-L28

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
omit [TopologicalSpace A] [DiscreteTopology A] [DiscreteTopology (Option A)]

theorem BalanceSpecification.MarkerExtension.mem_endingMarkerFinset {X : ShiftSpace (Option A)} {n : ℕ} {w : Word (Option A)} :
    w ∈ endingMarkerFinset X n ↔ w ∈ language X ∧ w.length = n ∧ ∃ u, w = u ++ [none] := by sorry
