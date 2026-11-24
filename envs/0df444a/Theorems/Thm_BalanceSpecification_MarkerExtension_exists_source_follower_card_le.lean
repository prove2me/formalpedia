-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_exists_source_follower_card_le
-- name    : BalanceSpecification.MarkerExtension.exists_source_follower_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:04:12.548939+00:00
-- url     : https://prove2.me/theorems/8d1d9652-d5c3-43fa-bfdb-c4850b1032cf
-- title:
--   Marker Extension: exists source follower card le
-- statement:
--   Alphabet renaming gives a genuine injection of finite follower sets.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerRight.lean#L67-L87
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerRight.lean#L67-L87

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
variable [Fintype A]

theorem BalanceSpecification.MarkerExtension.exists_source_follower_card_le
    (hmarker : IsSynchronizing (language X) [none])
    (hF : ∀ v ∈ language Y, [none] ++ v.map some ∈ language X)
    (hNonMarker : ∀ u ∈ language X, none ∉ u →
      ∃ v ∈ language Y, u = v.map some)
    {u : Word (Option A)} (hu : u ∈ language X) :
    ∃ v ∈ language Y, ∀ n : ℕ,
      (followerFinset (language Y) v n).card ≤
        (followerFinset (language X) u n).card := by sorry
