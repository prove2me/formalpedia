-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_truncSum_coupled
-- name    : FixedNumerator.QuarticData.truncSum_coupled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:40:04.92857+00:00
-- url     : https://prove2.me/theorems/ffb0a5e0-7779-4c72-a332-a939de80b26b
-- title:
--   Quartic Data: trunc Sum coupled
-- statement:
--   **Corollary 2.3, cases `r = 0` and `r = 2`: the coupled pair.** For `μ'` prime to `π`, the
--   numerators `μ'` and `π² μ'` are linked by
--   `S_γ(μ', β) = S_{πγ}(μ', β) + (-1)^{C(πβ, π)} g₄(μ', π) W(π) S_{πγ}(π² μ', πβ)(X / N(π))` and
--   `S_γ(π² μ', πβ) = S_{πγ}(π² μ', πβ) + (-1)^{C(β, π³)} g₄(π² μ', π³) W(π)³ S_{πγ}(μ', β)(X / N(π)³)`.
--   These are DDHL (8.6) and (8.7); eliminating gives (8.8).
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L177-L209
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L177-L209

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

theorem FixedNumerator.QuarticData.truncSum_coupled (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (X : ℕ) :
    truncSum D W μ' β γ X = truncSum D W μ' β (π * γ) X +
        (-1 : ℂ) ^ C (π * β) π * D.g μ' π * W π *
          truncSum D W (π ^ 2 * μ') (π * β) (π * γ) (X / π.norm.toNat) ∧
      truncSum D W (π ^ 2 * μ') (π * β) γ X = truncSum D W (π ^ 2 * μ') (π * β) (π * γ) X +
        (-1 : ℂ) ^ C β (π ^ 3) * D.g (π ^ 2 * μ') (π ^ 3) * W π ^ 3 *
          truncSum D W μ' β (π * γ) (X / π.norm.toNat ^ 3) := by sorry
