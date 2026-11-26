-- Prove2me | Theorems.Thm_FixedNumerator_numerator_period
-- name    : FixedNumerator.numerator_period
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:45.068389+00:00
-- url     : https://prove2.me/theorems/c26acf0c-ee06-4c25-9c1d-b675a5ac2a65
-- title:
--   Fixed Numerator: numerator period
-- statement:
--   **Periodicity in the numerator**: `g₄(μ π^{4j}, c) = g₄(μ, c)` for primary `c` prime to `π`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L40-L42
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L40-L42

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

theorem FixedNumerator.numerator_period (D : QuarticData) (μ π c : GaussianInt) (hc : IsPrimary c)
    (hcop : IsCoprime π c) (j : ℕ) : D.g (μ * π ^ (4 * j)) c = D.g μ c := by sorry
