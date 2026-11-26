-- Prove2me | Theorems.Thm_FixedNumerator_lemma_2_2
-- name    : FixedNumerator.lemma_2_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:07.703212+00:00
-- url     : https://prove2.me/theorems/dc265deb-1f8d-49c1-ba2c-a23a3a774b09
-- title:
--   Fixed Numerator: lemma 2 2
-- statement:
--   **Lemma 2.2, the splitting identity for truncated sums.** For a primary prime `π` prime to
--   `γ`, a primary `β`, and a completely multiplicative weight `W` (standing for
--   `(c/|c|)^ℓ N(c)^{-s}`),
--   `∑_{N(c) ≤ X, c ≡ β, (c, γ) = 1} g₄(μ, c) W(c)` equals
--   `∑_{k ≤ X} (-1)^{C(π^k β, π^k)} g₄(μ, π^k) W(π)^k ∑_{N(c') ≤ X / N(π)^k, c' ≡ π^k β, (c', πγ) = 1}
--   g₄(μ π^{2k}, c') W(c')`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L66-L72
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L66-L72

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

theorem FixedNumerator.lemma_2_2 (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (X : ℕ) :
    truncSum D W μ β γ X =
      ∑ k ∈ range (X + 1), (-1 : ℂ) ^ C (π ^ k * β) (π ^ k) * D.g μ (π ^ k) * W π ^ k *
        truncSum D W (μ * π ^ (2 * k)) (π ^ k * β) (π * γ) (X / π.norm.toNat ^ k) := by sorry
