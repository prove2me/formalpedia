-- Prove2me | Theorems.Thm_BalanceSpecification_weighted_sum_le_of_geometric_bound
-- name    : BalanceSpecification.weighted_sum_le_of_geometric_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:46.059153+00:00
-- url     : https://prove2.me/theorems/474e8f8d-ad38-456e-91cc-cab526379f9a
-- title:
--   Balance Specification: weighted sum le of geometric bound
-- statement:
--   A slower geometric family has a uniformly bounded pressure at a larger base.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/RenewalBounds.lean#L88-L105
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/RenewalBounds.lean#L88-L105

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.weighted_sum_le_of_geometric_bound
    {b : ℕ → ℝ} {θ ρ C : ℝ} (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hθρ : θ < ρ)
    (hC : 0 ≤ C) (hb : ∀ l : ℕ, b l ≤ C * θ ^ l) (n : ℕ) :
    (∑ l ∈ Finset.range (n + 1), b l / ρ ^ l) ≤ C / (1 - θ / ρ) := by sorry
