-- Prove2me | Theorems.Thm_FixedNumerator_QuarticData_truncSum_split
-- name    : FixedNumerator.QuarticData.truncSum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:36:30.110239+00:00
-- url     : https://prove2.me/theorems/8dcfaf96-8a96-55f6-b334-aaf8aaf9ec42
-- title:
--   Quartic Data: trunc Sum split
-- statement:
--   **Lemma 2.2, the splitting identity for truncated sums.**
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L114-L191
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Split.lean#L114-L191

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)

theorem FixedNumerator.QuarticData.truncSum_split (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ : GaussianInt} (μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (X : ℕ) :
    truncSum D W μ β γ X =
      ∑ k ∈ range (X + 1), (-1 : ℂ) ^ C (π ^ k * β) (π ^ k) * D.g μ (π ^ k) * W π ^ k *
        truncSum D W (μ * π ^ (2 * k)) (π ^ k * β) (π * γ) (X / π.norm.toNat ^ k) := by sorry
