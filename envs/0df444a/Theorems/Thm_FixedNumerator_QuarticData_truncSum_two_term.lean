-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_truncSum_two_term
-- name    : FixedNumerator.QuarticData.truncSum_two_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:37:23.635041+00:00
-- url     : https://prove2.me/theorems/445a074a-34ac-5895-8843-4b6bad7fced3
-- title:
--   Quartic Data: trunc Sum two term
-- statement:
--   The splitting identity with two surviving terms.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L74-L96
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L74-L96

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)

theorem FixedNumerator.QuarticData.truncSum_two_term (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ : GaussianInt} (μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) {m : ℕ} (hm : m ≠ 0)
    (hsupp : ∀ k, k ≠ 0 → k ≠ m → D.g μ (π ^ k) = 0) (X : ℕ) :
    truncSum D W μ β γ X = truncSum D W μ β (π * γ) X +
      (-1 : ℂ) ^ C (π ^ m * β) (π ^ m) * D.g μ (π ^ m) * W π ^ m *
        truncSum D W (μ * π ^ (2 * m)) (π ^ m * β) (π * γ) (X / π.norm.toNat ^ m) := by sorry
