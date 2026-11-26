-- Prove2me | Theorems.Thm_FixedNumerator_corollary_2_3_reduce
-- name    : FixedNumerator.corollary_2_3_reduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:50.371587+00:00
-- url     : https://prove2.me/theorems/fa423e86-035b-4860-acbc-a6b2c1b027f7
-- title:
--   Fixed Numerator: corollary 2 3 reduce
-- statement:
--   **Corollary 2.3, first claim: reduction of the valuation.** On the series prime to `π`, the
--   numerator `π^e μ'` may be replaced by `π^{e mod 4} μ'`, for every `e`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L123-L126
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L123-L126

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator

theorem FixedNumerator.corollary_2_3_reduce (D : QuarticData) (W : GaussianInt → ℂ) (π γ μ' β : GaussianInt)
    (hβ : IsPrimary β) (e X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X = truncSum D W (π ^ (e % 4) * μ') β (π * γ) X := by sorry
