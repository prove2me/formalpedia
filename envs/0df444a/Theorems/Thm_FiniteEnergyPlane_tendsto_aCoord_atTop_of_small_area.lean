-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendsto_aCoord_atTop_of_small_area
-- name    : FiniteEnergyPlane.tendsto_aCoord_atTop_of_small_area
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T16:25:10.75423+00:00
-- url     : https://prove2.me/theorems/1af782b1-bad6-453e-b489-1022a31fd8e0
-- title:
--   Planes with small area outside shrinking disks escape to $+\infty$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $T>0$, let $\gamma>0$ be smaller than every period at most $T$ of a periodic Reeb orbit, and let $e>0$ and $N\in\mathbb{R}$. Let $r_k\to0^+$ and let $v_k$ be finite-energy $\tilde J$-holomorphic planes with
--   1. $E(v_k)\le T$ and $\int_{\{|z|>r_k\}}v_k^*d\lambda\le\gamma$;
--   2. $\int_{|z|=\rho}v_k^*\lambda\ge e$ for every counterclockwise circle of radius $\rho>r_k$;
--   3. $a(v_k(z))\ge-N$ for all $k$ and $z$.
--
--   Then $\inf_{z\in K}a(v_k(z))\to+\infty$ for every compact $K\subset\mathbb{C}\setminus\{0\}$.
--
--   **Formalization Note** The conclusion is stated without an infimum: for every compact $K\not\ni0$ and every $M$, eventually $M\le a(v_k(z))$ for all $z\in K$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 4.16

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 4.16. Let `T > 0` and let `0 < γ` be smaller than every
period at most `T` of a periodic Reeb orbit. Let `rₖ → 0⁺`, `e > 0` and `N`, and let `vₖ` be
finite-energy `J̃`-holomorphic planes with energy at most `T`, `dλ`-energy at most `γ` on
`{|z| > rₖ}`, action `∫_{|z| = ρ} vₖ*λ ≥ e` on every counterclockwise circle of radius `ρ > rₖ`,
and `aCoord H ∘ vₖ ≥ -N` everywhere. Then `aCoord H ∘ vₖ → +∞` uniformly on every compact subset
of `ℂ \ {0}`. -/
theorem tendsto_aCoord_atTop_of_small_area {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (T γ e N : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ T → γ < Q.T) (he : 0 < e)
    (r : ℕ → ℝ) (hr0 : ∀ k, 0 < r k) (hr : Tendsto r atTop (𝓝 0)) (v : ℕ → ℂ → V n)
    (hv : ∀ k, IsFiniteEnergyCurve H J Set.univ (v k))
    (hE : ∀ k, energy H Set.univ (v k) ≤ ENNReal.ofReal T)
    (hdl : ∀ k, dlambdaEnergy H {z | r k < ‖z‖} (v k) ≤ ENNReal.ofReal γ)
    (hact : ∀ k, ∀ ρ : ℝ, r k < ρ → e ≤ loopAction H (v k) (ccwLoop ρ))
    (hN : ∀ k z, -N ≤ aCoord H (v k z)) :
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
      ∀ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ Kc, M ≤ aCoord H (v k z) := by
  sorry

end FiniteEnergyPlane
