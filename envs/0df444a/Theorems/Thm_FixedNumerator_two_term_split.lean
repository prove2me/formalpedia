-- Prove2me | Theorems.Thm_FixedNumerator_two_term_split
-- name    : FixedNumerator.two_term_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:59.31193+00:00
-- url     : https://prove2.me/theorems/8d896a81-f2b2-43e7-9038-0f22b79b4546
-- title:
--   Fixed Numerator: two term split
-- statement:
--   **The splitting identity with two terms**, when `g₄(μ, π^k)` vanishes except at `k = 0, m`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L75-L82
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L75-L82

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

theorem FixedNumerator.two_term_split (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (m : ℕ) (hm : m ≠ 0)
    (hsupp : ∀ k, k ≠ 0 → k ≠ m → D.g μ (π ^ k) = 0) (X : ℕ) :
    truncSum D W μ β γ X = truncSum D W μ β (π * γ) X +
      (-1 : ℂ) ^ C (π ^ m * β) (π ^ m) * D.g μ (π ^ m) * W π ^ m *
        truncSum D W (μ * π ^ (2 * m)) (π ^ m * β) (π * γ) (X / π.norm.toNat ^ m) := by sorry
