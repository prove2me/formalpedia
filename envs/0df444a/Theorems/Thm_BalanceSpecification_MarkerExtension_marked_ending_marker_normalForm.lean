-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_marked_ending_marker_normalForm
-- name    : BalanceSpecification.MarkerExtension.marked_ending_marker_normalForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:44.844831+00:00
-- url     : https://prove2.me/theorems/e9acd590-f862-497b-a262-1e844282deba
-- title:
--   Marker Extension: marked ending marker normal Form
-- statement:
--   The boundary form of every admissible word ending in a marker: an initial
--   marker-free suffix, then complete generators, then the final marker.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L233-L257
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L233-L257

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
omit [TopologicalSpace A] [DiscreteTopology A] [Fintype A]

theorem BalanceSpecification.MarkerExtension.marked_ending_marker_normalForm {P : Set (Word A)} {z : Word (Option A)}
    (hz : z ++ [none] ∈ language (codedShift (markedCode P))) :
    ∃ a : Word A, ∃ c : Word (Option A),
      a.map some ++ [none] ∈ language (codedShift (markedCode P)) ∧
      c ∈ generatedWords (markedCode P) ∧ z ++ [none] = a.map some ++ c ++ [none] := by sorry
