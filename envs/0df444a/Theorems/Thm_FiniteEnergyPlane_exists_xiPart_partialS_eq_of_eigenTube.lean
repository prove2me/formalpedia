-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_xiPart_partialS_eq_of_eigenTube
-- name    : FiniteEnergyPlane.exists_xiPart_partialS_eq_of_eigenTube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T10:15:30.611571+00:00
-- url     : https://prove2.me/theorems/7d3b211f-804f-483d-b256-ae31606ad90f
-- title:
--   The transverse derivative of a half-cylinder with an eigenvector leading term follows the eigenvector
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with Reeb field $R$ and contact structure $\xi$, and $P=(x,T)$ a periodic Reeb orbit. Let $v$ be a smooth $1$-periodic loop with $v(t)\in\xi_{x(Tt)}$ for every $t$, and let $\kappa<0$, $\varepsilon,c\in\mathbb{R}$. Let $\tau:\mathbb{R}^2\to\mathbb{R}$ and $r:\mathbb{R}^2\to\mathbb{R}^{2n+2}$ be such that $\tau(s,t)-\varepsilon Tt-c\to0$ and $r\to0$ in $C^\infty$ as $s\to+\infty$, and suppose that for $s\ge s_0$
--   $$W(s,t)=\mathrm{proj}\Big(x(\tau(s,t))+e^{\kappa s}\big(v(\tau(s,t)/T)+r(s,t)\big)\Big),$$
--   where $\mathrm{proj}$ is the radial projection onto $S$. For $w\in S$ let $\pi_w u=u-\frac{dH(w)u}{dH(w)w}\,w-\lambda_0(w)(u)\,R(w)$ be the projection onto $\xi_w$ along $w$ and $R(w)$. Then for every $\delta>0$ there is $s_1$ such that for all $s\ge s_1$ and all $t$:
--
--   1. $|W(s,t)-x(\tau(s,t))|\le\delta$, and
--   2. there are $\sigma>0$ and $e\in\mathbb{R}^{2n+2}$ with $|e|\le\delta$ and
--   $$\pi_{W(s,t)}\,\partial_sW(s,t)=\sigma\,\kappa\,\big(v(\tau(s,t)/T)+e\big).$$
--
--   So, up to a positive factor, the $\xi$-part of $\partial_sW$ is asymptotic to $\kappa$ times the eigenvector term, uniformly in $t$. This identifies the direction of $\pi\,\partial_s u$ near a puncture where an asymptotic eigenvector description holds, for example to compute asymptotic winding numbers.
--
--   **Formalization Note** "Tends to $0$ in $C^\infty$" is `TendstoZeroCInfty`; $\partial_sW(s,t)$ is `fderiv ℝ W (s, t) (1, 0)`; $\lambda_0$ is `liouville` and $R$ is `reeb H`. The loop $v$ is `IsXiLoop P v` (no nonvanishing assumption). Nothing is assumed about $W$ for $s<s_0$.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 and Lemma 2.16; H. Hofer, K. Wysocki, E. Zehnder, Geom. Funct. Anal. 5 (1995), Section 3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P = (x, T)` be a periodic Reeb orbit on a strictly star-shaped level, `v` a `ξ`-loop along
`P`, and `κ < 0`. Suppose that for `s ≥ s₀`
`W(s, t) = proj H (x(τ) + e^{κs} (v(τ / T) + r))`, where `τ(s, t) - εTt - c → 0` and `r → 0` in
`C^∞`. Then for every `δ > 0` there is `s₁` such that for all `s ≥ s₁` and all `t`:
`W(s, t)` is within `δ` of `x(τ(s, t))`, and the `ξ`-part of `∂ₛW`, its projection
`π_W d = d - (dH(W) d / dH(W) W) W - λ₀(W)(d) R(W)` onto `ξ_W` along `W` and `R(W)`, equals
`σ κ (v(τ(s, t) / T) + e)` for some `σ > 0` and some `e` with `‖e‖ ≤ δ`. -/
theorem exists_xiPart_partialS_eq_of_eigenTube {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (κ ε c s₀ : ℝ) (hκ : κ < 0)
    (v : ℝ → V n) (hv : IsXiLoop P v)
    (τ : ℝ × ℝ → ℝ) (r : ℝ × ℝ → V n) (W : ℝ × ℝ → V n)
    (hτ : TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c))
    (hr : TendstoZeroCInfty r)
    (hW : ∀ s ≥ s₀, ∀ t : ℝ, W (s, t) =
      proj H (P.x (τ (s, t)) + Real.exp (κ * s) • (v (τ (s, t) / P.T) + r (s, t))))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖W (s, t) - P.x (τ (s, t))‖ ≤ δ ∧
      ∃ σ > 0, ∃ e : V n, ‖e‖ ≤ δ ∧
        let w := W (s, t)
        let d := fderiv ℝ W (s, t) (1, 0)
        d - (fderiv ℝ H w d / fderiv ℝ H w w) • w - liouville w d • reeb H w =
          (σ * κ) • (v (τ (s, t) / P.T) + e) := by
  sorry

end FiniteEnergyPlane
