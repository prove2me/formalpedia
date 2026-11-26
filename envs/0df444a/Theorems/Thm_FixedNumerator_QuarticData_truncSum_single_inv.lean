-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_truncSum_single_inv
-- name    : FixedNumerator.QuarticData.truncSum_single_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:40:05.338096+00:00
-- url     : https://prove2.me/theorems/878ce254-426d-40a3-86f6-1fc8c5a543d9
-- title:
--   Quartic Data: trunc Sum single inv
-- statement:
--   **The inverse of Corollary 2.3, cases `r = 1, 3`**, the truncated form of
--   `ψ*(s, μ; πγ) = Δ(s)⁻¹ ψ*(s, μ; γ)`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L156-L170
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L156-L170

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

theorem FixedNumerator.QuarticData.truncSum_single_inv (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    {e : ℕ} (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X =
      ∑ j ∈ range (X + 1), (-(D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1))) ^ j *
        truncSum D W (π ^ e * μ') β γ (X / (π.norm.toNat ^ (e + 1)) ^ j) := by sorry
