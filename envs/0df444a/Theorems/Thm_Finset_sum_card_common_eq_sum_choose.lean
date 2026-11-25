-- Prove2me | Theorems.Thm_Finset_sum_card_common_eq_sum_choose
-- name    : Finset.sum_card_common_eq_sum_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:58:32.613742+00:00
-- url     : https://prove2.me/theorems/14bed10a-dd5e-46a4-9539-7d5a14628d87
-- title:
--   Finset: sum card common eq sum choose
-- statement:
--   **Common-neighbour moments.** For a relation `r` between `α` and `β`, summing over the
--   `h`-subsets `U` of `L` the number of `y ∈ R` related to all of `U` gives
--   `∑ y ∈ R, C(deg y, h)`, where `deg y` counts the `x ∈ L` related to `y`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L58-L77
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/DependentRandomChoice.lean#L58-L77

module
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_DependentRandomChoice
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α β : Type*}

theorem Finset.sum_card_common_eq_sum_choose (r : α → β → Prop) [∀ x y, Decidable (r x y)]
    (L : Finset α) (R : Finset β) (h : ℕ) :
    ∑ U ∈ L.powersetCard h, #{y ∈ R | ∀ x ∈ U, r x y} =
      ∑ y ∈ R, (#{x ∈ L | r x y}).choose h := by sorry
