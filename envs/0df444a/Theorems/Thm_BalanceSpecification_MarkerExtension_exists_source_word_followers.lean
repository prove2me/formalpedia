-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_exists_source_word_followers
-- name    : BalanceSpecification.MarkerExtension.exists_source_word_followers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:06.753407+00:00
-- url     : https://prove2.me/theorems/1a8412a2-5bc8-43ea-8e7e-0a2e4cdd4753
-- title:
--   Marker Extension: exists source word followers
-- statement:
--   Every extension word has a source word whose followers remain followers
--   under the injective alphabet renaming. The last marker is the gluing point.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerRight.lean#L37-L62
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerRight.lean#L37-L62

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerRight
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [TopologicalSpace (Option A)]
  {Y : ShiftSpace A} {X : ShiftSpace (Option A)}

theorem BalanceSpecification.MarkerExtension.exists_source_word_followers
    (hmarker : IsSynchronizing (language X) [none])
    (hF : ∀ v ∈ language Y, [none] ++ v.map some ∈ language X)
    (hNonMarker : ∀ u ∈ language X, none ∉ u →
      ∃ v ∈ language Y, u = v.map some)
    {u : Word (Option A)} (hu : u ∈ language X) :
    ∃ v ∈ language Y, ∀ w ∈ language Y, v ++ w ∈ language Y →
      u ++ w.map some ∈ language X := by sorry
