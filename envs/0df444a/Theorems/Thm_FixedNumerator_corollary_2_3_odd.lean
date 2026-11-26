-- Prove2me | Theorems.Thm_FixedNumerator_corollary_2_3_odd
-- name    : FixedNumerator.corollary_2_3_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:12.958664+00:00
-- url     : https://prove2.me/theorems/ebe7727b-d6a6-501b-b494-b6db35454bb1
-- title:
--   Fixed Numerator: corollary 2 3 odd
-- statement:
--   **Corollary 2.3, cases `r = 1` and `r = 3`.** For `μ = π^e μ'` with `e ∈ {1, 3}` and `μ'`
--   prime to `π`: `S_γ(X) = S_{πγ}(X) + g₄(μ, π^{e+1}) W(π)^{e+1} S_{πγ}(X / N(π)^{e+1})`, the
--   truncated form of `ψ*(s, μ; γ) = Δ(s) ψ*(s, μ; πγ)`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L87-L94
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L87-L94

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

theorem FixedNumerator.corollary_2_3_odd (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e : ℕ) (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X = truncSum D W (π ^ e * μ') β (π * γ) X +
      D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1) *
        truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (e + 1)) := by sorry
