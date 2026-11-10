-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_eq_7_1_7_2
-- name    : AlgCoverage.OddOrder.eq_7_1_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:25.93276+00:00
-- url     : https://prove2.me/theorems/2f3d3fc0-e189-4b51-b72f-12deaffb0bc5
-- title:
--   §7, Eqs. (7.1)–(7.2) — convolution of subprobabilities below Haar: $\mu_1*\mu_2=(1-\delta_1-\delta_2)u_K+\nu_1*\nu_2$ and $|K|^{-1}\gamma\le\mu_1*\mu_2\le|K|^{-1}$
-- statement:
--   Let $K$ be a finite group with Haar probability $u_K(z)=|K|^{-1}$, and let $\mu_1,\mu_2$ be subprobabilities on $K$ with $\mu_i\le u_K$ pointwise and masses $\sum_z\mu_i(z)=1-\delta_i$. Put $\nu_i=u_K-\mu_i$. Then
--   $$\mu_1*\mu_2=(1-\delta_1-\delta_2)\,u_K+\nu_1*\nu_2, \tag{7.1}$$
--   and therefore, with $\gamma=(1-\delta_1-\delta_2)_+$, for every $z\in K$,
--   $$|K|^{-1}\gamma\le(\mu_1*\mu_2)(z)\le|K|^{-1}. \tag{7.2}$$
--   No commutativity is assumed.
--
--   Differences from the source: none.
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 22 (PDF 23), §7, Eqs. (7.1)–(7.2)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Convolution

namespace AlgCoverage.OddOrder

/-- §7, Eqs. (7.1)–(7.2), Lin, printed p. 22 / PDF 23. For a finite group `K` and subprobabilities
`μ₁, μ₂ ≤ u_K` pointwise with masses `1 − δ₁, 1 − δ₂`, and `ν_i = u_K − μ_i`:
`μ₁ ∗ μ₂ = (1 − δ₁ − δ₂) u_K + ν₁ ∗ ν₂` (7.1), and with `γ = (1 − δ₁ − δ₂)₊`,
`|K|⁻¹ γ ≤ (μ₁ ∗ μ₂)(z) ≤ |K|⁻¹` for every `z` (7.2). No commutativity. -/
theorem eq_7_1_7_2 (K : Type*) [Group K] [Fintype K] (μ₁ μ₂ : K → ℝ)
    (h₁ : IsSubprob μ₁) (h₂ : IsSubprob μ₂)
    (hle₁ : ∀ z, μ₁ z ≤ haar K z) (hle₂ : ∀ z, μ₂ z ≤ haar K z)
    (δ₁ δ₂ : ℝ) (hδ₁ : ∑ z, μ₁ z = 1 - δ₁) (hδ₂ : ∑ z, μ₂ z = 1 - δ₂) :
    (∀ z, conv μ₁ μ₂ z = (1 - δ₁ - δ₂) * haar K z +
        conv (fun w => haar K w - μ₁ w) (fun w => haar K w - μ₂ w) z) ∧
    ∀ z, max (1 - δ₁ - δ₂) 0 / (Fintype.card K : ℝ) ≤ conv μ₁ μ₂ z ∧
      conv μ₁ μ₂ z ≤ 1 / (Fintype.card K : ℝ) := by sorry

end AlgCoverage.OddOrder
