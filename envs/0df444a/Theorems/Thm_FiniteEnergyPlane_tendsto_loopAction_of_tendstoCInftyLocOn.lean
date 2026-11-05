-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendsto_loopAction_of_tendstoCInftyLocOn
-- name    : FiniteEnergyPlane.tendsto_loopAction_of_tendstoCInftyLocOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T19:51:36.152803+00:00
-- url     : https://prove2.me/theorems/ad5d151d-cc8c-43cb-a9d0-842903527b2e
-- title:
--   Loop actions converge under $C^\infty_{loc}$ convergence
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $U\subseteq\mathbb{C}$ open, and $u_k,u_0:\mathbb{C}\to\mathbb{R}^{2n+2}$ maps that are $C^\infty$ on $U$ and do not vanish on $U$. If $u_k\to u_0$ in $C^\infty_{loc}(U)$, then for every smooth loop $\gamma:\mathbb{R}\to U$
--   $$\int_0^1\lambda_0\big(\ell_k(t)\big)\,\ell_k'(t)\,dt\;\longrightarrow\;\int_0^1\lambda_0\big(\ell_0(t)\big)\,\ell_0'(t)\,dt,\qquad \ell_k=\mathrm{proj}\circ u_k\circ\gamma,$$
--   that is, the actions $\int_\gamma u_k^*\lambda$ converge to $\int_\gamma u_0^*\lambda$.
--
--   **Formalization Note** $C^\infty_{loc}(U)$ convergence is `JHolomorphic.TendstoCInftyLocOn`: every derivative converges uniformly on every compact subset of $U$. The action is `loopAction` along $\gamma$; only $t\in[0,1]$ enters.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, § 4 (supporting lemma for Lemma 4.16)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `S = H⁻¹(1)` be strictly star-shaped, `U ⊆ ℂ` open, and `u k → u₀` in `C^∞_loc(U)`, where
all maps are `C^∞` on `U` and avoid `0` there. Then for every smooth loop `γ : ℝ → ℂ` with image
in `U`, the loop actions `loopAction H (u k) γ` converge to `loopAction H u₀ γ`. -/
theorem tendsto_loopAction_of_tendstoCInftyLocOn {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (U : Set ℂ) (hU : IsOpen U) (u : ℕ → ℂ → V n)
    (u₀ : ℂ → V n) (hu : ∀ k, ContDiffOn ℝ ∞ (u k) U) (hu₀ : ContDiffOn ℝ ∞ u₀ U)
    (hne : ∀ k, ∀ z ∈ U, u k z ≠ 0) (hne₀ : ∀ z ∈ U, u₀ z ≠ 0)
    (hconv : JHolomorphic.TendstoCInftyLocOn u u₀ U) (γ : ℝ → ℂ) (hγ : ContDiff ℝ ∞ γ)
    (hγU : ∀ t, γ t ∈ U) :
    Tendsto (fun k => loopAction H (u k) γ) atTop (𝓝 (loopAction H u₀ γ)) := by
  sorry

end FiniteEnergyPlane
