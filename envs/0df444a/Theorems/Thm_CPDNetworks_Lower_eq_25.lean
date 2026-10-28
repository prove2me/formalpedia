-- Prove2me | Theorems.Thm_CPDNetworks_Lower_eq_25
-- name    : CPDNetworks.Lower.eq_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:53.857994+00:00
-- url     : https://prove2.me/theorems/7ab44166-1b7a-4e13-8829-d5c95c229aeb
-- title:
--   Display (25) — mixture lower bound: type II error ≥ 1 − ½‖p₁ − p₀‖₁ − α ≥ 1 − ½(χ²(p₁, p₀))^{1/2} − α
-- statement:
--   Fix $n$, $T$, a change point $\tau$, a sparsity level $\omega_n$ and an energy $R$. Let $\psi$ be any test of level $\alpha$, that is, with type I error $\alpha(\psi)\le\alpha$ over $\mathcal S_n(\omega_n)$. Let $\pi_{n,0}$ be a finitely supported prior on $\mathcal S_n(\omega_n)$, putting weight $w_{0,k}\ge0$ on $(\Theta^0_k,\Pi^0_k)$, and $\pi_{n,1}$ a finitely supported prior on $\mathcal W^\tau_{n,T}(\omega_n,R)$, putting weight $w_{1,k}\ge0$ on $\{(\Theta^a_k,\Pi_k),(\Theta^b_k,\Pi_k)\}$, with weights summing to $1$. Let
--   $$p_0(Y)=\sum_kw_{0,k}\,\mathrm P_{(\Theta^0_k,\Pi^0_k)}(Y),\qquad p_1(Y)=\sum_kw_{1,k}\,\mathrm P_{(\Theta^a_k,\Pi_k),(\Theta^b_k,\Pi_k)}(Y)$$
--   be the mixture laws of the observations. Then the type II error of $\psi$ in problem (P1) satisfies
--   $$\beta(\psi,R)\ \ge\ 1-\frac12\sum_Y|p_1(Y)-p_0(Y)|-\alpha,$$
--   and, if $p_0(Y)>0$ for every observation $Y$,
--   $$\beta(\psi,R)\ \ge\ 1-\frac12\Big(\mathrm E_0\Big[\frac{p_1}{p_0}(Y)\Big]^2-1\Big)^{1/2}-\alpha.$$
--
--   This is the reduction of the minimax lower bound to a bound on the $\chi^2$-divergence between two mixtures (the "fuzzy hypotheses" or second moment method of Ingster and Suslina).
--
--   **Formalization Note** The page writes $\|p_1-p_0\|_{\mathrm{TV}}$; as in display (9) of the paper, $\|\cdot\|$ here is the $L^1$ distance $\sum_Y|p_1(Y)-p_0(Y)|$, and that is what is stated. The priors are finitely supported with arbitrary weights, which covers the paper's priors (a point mass under $H_0$, the uniform law on $2^n$ sign vectors under $H_1$). The square root is applied to $\mathrm E_0[(p_1/p_0)^2]-1=\chi^2(p_1,p_0)\ge0$.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 33, App. B.1, display (25)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting

namespace CPDNetworks.Lower

open scoped Matrix

/-- **Display (25)** (Enikeeva–Klopp, App. B.1, p. 33): the mixture (fuzzy hypotheses) lower bound.
Let `ψ` be any test of level `α` (type I error `≤ α` over `𝒮_n(ω_n)`). Let `π_{n,0}` be a finitely
supported prior with weights `w₀` on null parameters `(Θ⁰_k, Π⁰_k) ∈ 𝒮_n(ω_n)`, and `π_{n,1}` a
finitely supported prior with weights `w₁` on alternatives
`{(Θᵃ_k, Π_k), (Θᵇ_k, Π_k)} ∈ 𝒲^τ_{n,T}(ω_n, R)`, and let `p₀`, `p₁` be the mixture laws of the
observations. Then the type II error of `ψ` at `τ` is at least `1 − ½‖p₁ − p₀‖₁ − α`, and, when
`p₀ > 0` everywhere, at least `1 − ½ (E₀[(p₁/p₀)²] − 1)^{1/2} − α`. -/
theorem eq_25 {n T : ℕ} (τ : ℕ) (ω α R : ℝ) (ψ : Obs n T → Bool) (hψ : typeI (T := T) ω ψ ≤ α)
    {K₀ K₁ : Type} [Fintype K₀] [Fintype K₁]
    (w₀ : K₀ → ℝ) (Θ₀ Pm₀ : K₀ → Matrix (Fin n) (Fin n) ℝ)
    (hw₀ : ∀ k, 0 ≤ w₀ k) (hw₀1 : ∑ k, w₀ k = 1) (hS : ∀ k, InS ω (Θ₀ k) (Pm₀ k))
    (w₁ : K₁ → ℝ) (Θa Θb Pm₁ : K₁ → Matrix (Fin n) (Fin n) ℝ)
    (hw₁ : ∀ k, 0 ≤ w₁ k) (hw₁1 : ∑ k, w₁ k = 1)
    (hW : ∀ k, InW T τ ω R (Θa k) (Θb k) (Pm₁ k)) :
    let p₀ : Obs n T → ℝ := fun y => ∑ k, w₀ k * weight (nullParam (T := T) (Θ₀ k) (Pm₀ k)) y
    let p₁ : Obs n T → ℝ := fun y => ∑ k, w₁ k * weight (altParam τ (Θa k) (Θb k) (Pm₁ k)) y
    1 - 1 / 2 * ∑ y, |p₁ y - p₀ y| - α ≤ typeII {τ} ω R ψ ∧
      ((∀ y, 0 < p₀ y) →
        1 - 1 / 2 * Real.sqrt (∑ y, p₁ y ^ 2 / p₀ y - 1) - α ≤ typeII {τ} ω R ψ) := by sorry

end CPDNetworks.Lower
