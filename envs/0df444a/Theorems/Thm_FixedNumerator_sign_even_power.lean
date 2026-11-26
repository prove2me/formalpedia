-- Prove2me | Theorems.Thm_FixedNumerator_sign_even_power
-- name    : FixedNumerator.sign_even_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:47.174832+00:00
-- url     : https://prove2.me/theorems/0d6dc28d-8d95-597a-bf15-ca5fa5e6b0e4
-- title:
--   Fixed Numerator: sign even power
-- statement:
--   For primary `π` and even `k`, `(-1)^{C(a, π^k)} = 1`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L56-L58
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L56-L58

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

theorem FixedNumerator.sign_even_power (π a : GaussianInt) (hπ : IsPrimary π) (k : ℕ) (hk : Even k) :
    (-1 : ℂ) ^ C a (π ^ k) = 1 := by sorry
