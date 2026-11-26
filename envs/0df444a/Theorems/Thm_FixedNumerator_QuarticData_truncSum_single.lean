-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_truncSum_single
-- name    : FixedNumerator.QuarticData.truncSum_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:38:14.33042+00:00
-- url     : https://prove2.me/theorems/6bb289e3-18e2-4c27-a64c-0e65185f1c08
-- title:
--   Quartic Data: trunc Sum single
-- statement:
--   **Corollary 2.3, cases `r = 1` and `r = 3`.** For `μ = π^e μ'` with `e ∈ {1, 3}` and `μ'` prime
--   to `π`, with `a = g₄(μ, π^{e+1}) W(π)^{e+1}`:
--   `S_γ(μ, β)(X) = S_{πγ}(μ, β)(X) + a S_{πγ}(μ, β)(X / N(π)^{e+1})`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L101-L123
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Cases.lean#L101-L123

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

theorem FixedNumerator.QuarticData.truncSum_single (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    {e : ℕ} (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X = truncSum D W (π ^ e * μ') β (π * γ) X +
      D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1) *
        truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (e + 1)) := by sorry
