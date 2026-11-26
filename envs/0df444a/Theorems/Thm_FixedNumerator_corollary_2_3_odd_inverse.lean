-- Prove2me | Theorems.Thm_FixedNumerator_corollary_2_3_odd_inverse
-- name    : FixedNumerator.corollary_2_3_odd_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:13.738675+00:00
-- url     : https://prove2.me/theorems/f6f84eb7-353b-5457-aa77-9053391a4b97
-- title:
--   Fixed Numerator: corollary 2 3 odd inverse
-- statement:
--   **The inverse of Corollary 2.3, cases `r = 1, 3`**, the truncated form of
--   `ψ*(s, μ; πγ) = Δ(s)⁻¹ ψ*(s, μ; γ)`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L98-L105
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L98-L105

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

theorem FixedNumerator.corollary_2_3_odd_inverse (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e : ℕ) (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X =
      ∑ j ∈ range (X + 1), (-(D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1))) ^ j *
        truncSum D W (π ^ e * μ') β γ (X / (π.norm.toNat ^ (e + 1)) ^ j) := by sorry
