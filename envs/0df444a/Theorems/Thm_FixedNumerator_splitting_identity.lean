-- Prove2me | Theorems.Thm_FixedNumerator_splitting_identity
-- name    : FixedNumerator.splitting_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:23.202931+00:00
-- url     : https://prove2.me/theorems/50bd3108-f995-5b80-838d-d8379ac93199
-- title:
--   Fixed Numerator: splitting identity
-- statement:
--   **The splitting identity.** For a primary `π` and a primary `c'` prime to `π`,
--   `g₄(μ, π^k c') = (-1)^{C(c', π^k)} g₄(μ, π^k) g₄(μ π^{2k}, c')`, with no condition linking `μ`
--   and `π`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L33-L37
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L33-L37

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

theorem FixedNumerator.splitting_identity (D : QuarticData) (μ π c' : GaussianInt) (hπ : IsPrimary π)
    (hc' : IsPrimary c') (hcop : IsCoprime π c') (k : ℕ) :
    D.g μ (π ^ k * c') =
      (-1 : ℂ) ^ C c' (π ^ k) * D.g μ (π ^ k) * D.g (μ * π ^ (2 * k)) c' := by sorry
