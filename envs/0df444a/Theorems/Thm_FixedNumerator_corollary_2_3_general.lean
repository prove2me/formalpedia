-- Prove2me | Theorems.Thm_FixedNumerator_corollary_2_3_general
-- name    : FixedNumerator.corollary_2_3_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:11.789042+00:00
-- url     : https://prove2.me/theorems/b37fd774-aaf9-44b6-843c-0ffc54a79dec
-- title:
--   Fixed Numerator: corollary 2 3 general
-- statement:
--   **Corollary 2.3 for every valuation.** For `μ = π^e μ'` with `μ'` prime to `π` and any
--   `e ≥ 0`, the terms of Lemma 2.2 that survive are `k = 4j ≤ e` and `k = e + 1`:
--   `S_γ(μ, β)(X) = ∑_{4j ≤ e} g₄(μ, π^{4j}) W(π)^{4j} S_{πγ}(μ, β)(X / N(π)^{4j})
--     + (-1)^{C(π^{e+1}β, π^{e+1})} g₄(μ, π^{e+1}) W(π)^{e+1} S_{πγ}(μ π^{2(e+1)}, π^{e+1}β)(X / N(π)^{e+1})`.
--   For `e ≤ 3` the sum has the single term `j = 0`; for `e = 5`, for example, the terms are
--   `k = 0, 4, 6`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L134-L145
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/Solution.lean#L134-L145

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

theorem FixedNumerator.corollary_2_3_general (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X =
      ∑ j ∈ range (e / 4 + 1), D.g (π ^ e * μ') (π ^ (4 * j)) * W π ^ (4 * j) *
          truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (4 * j)) +
        (-1 : ℂ) ^ C (π ^ (e + 1) * β) (π ^ (e + 1)) * D.g (π ^ e * μ') (π ^ (e + 1)) *
          W π ^ (e + 1) *
          truncSum D W (π ^ e * μ' * π ^ (2 * (e + 1))) (π ^ (e + 1) * β) (π * γ)
            (X / π.norm.toNat ^ (e + 1)) := by sorry
