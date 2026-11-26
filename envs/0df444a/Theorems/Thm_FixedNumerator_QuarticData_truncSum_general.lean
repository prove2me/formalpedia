-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_truncSum_general
-- name    : FixedNumerator.QuarticData.truncSum_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:39:47.333232+00:00
-- url     : https://prove2.me/theorems/176f729e-b471-510d-ad22-7f35ca8d6a44
-- title:
--   Quartic Data: trunc Sum general
-- statement:
--   **Corollary 2.3 for every valuation.** For `μ = π^e μ'`, `μ'` prime to `π`, and any `e`,
--   `S_γ(μ, β)(X) = ∑_{4j ≤ e} g₄(μ, π^{4j}) W(π)^{4j} S_{πγ}(μ, β)(X / N(π)^{4j})
--     + (-1)^{C(π^{e+1}β, π^{e+1})} g₄(μ, π^{e+1}) W(π)^{e+1} S_{πγ}(μ π^{2(e+1)}, π^{e+1}β)(X / N(π)^{e+1})`.
--   The term `j = 0` is `S_{πγ}(μ, β)(X)`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/General.lean#L38-L108
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/General.lean#L38-L108

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_General
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)

theorem FixedNumerator.QuarticData.truncSum_general (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X =
      ∑ j ∈ range (e / 4 + 1), D.g (π ^ e * μ') (π ^ (4 * j)) * W π ^ (4 * j) *
          truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (4 * j)) +
        (-1 : ℂ) ^ C (π ^ (e + 1) * β) (π ^ (e + 1)) * D.g (π ^ e * μ') (π ^ (e + 1)) *
          W π ^ (e + 1) *
          truncSum D W (π ^ e * μ' * π ^ (2 * (e + 1))) (π ^ (e + 1) * β) (π * γ)
            (X / π.norm.toNat ^ (e + 1)) := by sorry
