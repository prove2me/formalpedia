-- Prove2me | Theorems.Thm_FiniteEnergyPlane_xiPart_partialS_ne_zero_of_eigenTube
-- name    : FiniteEnergyPlane.xiPart_partialS_ne_zero_of_eigenTube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T16:37:07.483106+00:00
-- url     : https://prove2.me/theorems/3e82a751-88ae-4362-ac84-a564ac478ea0
-- title:
--   The transverse derivative of a half-cylinder with an eigenvector leading term vanishes nowhere
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with Reeb field $R$ and contact structure $\xi$, and $P=(x,T)$ a periodic Reeb orbit. Let $v$ be a smooth $1$-periodic loop with $v(t)\in\xi_{x(Tt)}$ and $v(t)\neq0$ for every $t$, and let $\kappa<0$, $\varepsilon,c\in\mathbb{R}$. Let $\tau:\mathbb{R}^2\to\mathbb{R}$ and $r:\mathbb{R}^2\to\mathbb{R}^{2n+2}$ be such that $\tau(s,t)-\varepsilon Tt-c\to0$ and $r\to0$ in $C^\infty$ as $s\to+\infty$, and suppose that for $s\ge s_0$
--   $$W(s,t)=\mathrm{proj}\Big(x(\tau(s,t))+e^{\kappa s}\big(v(\tau(s,t)/T)+r(s,t)\big)\Big),$$
--   where $\mathrm{proj}$ is the radial projection onto $S$. For $w\in S$ let $\pi_w u=u-\frac{dH(w)u}{dH(w)w}\,w-\lambda_0(w)(u)\,R(w)$ be the projection onto $\xi_w$ along $w$ and $R(w)$. Then there is $s_1$ such that $\pi_{W(s,t)}\,\partial_sW(s,t)\neq0$ for all $s\ge s_1$ and all $t$.
--
--   This is the step that turns an asymptotic eigenvector description of a pseudoholomorphic half-cylinder into the nonvanishing of $\pi\,du$ near the puncture.
--
--   **Formalization Note** "Tends to $0$ in $C^\infty$" is `TendstoZeroCInfty`; $\partial_sW(s,t)$ is `fderiv ℝ W (s, t) (1, 0)`; $\lambda_0$ is `liouville` and $R$ is `reeb H`. Nothing is assumed about $W$ for $s<s_0$.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 2.9 (3) and Theorem 2.11; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P = (x, T)` be a periodic Reeb orbit on a strictly star-shaped level, `v` a `ξ`-loop along
`P` that vanishes nowhere, and `κ < 0`. Suppose that for `s ≥ s₀`
`W(s, t) = proj H (x(τ) + e^{κs} (v(τ / T) + r))`, where `τ(s, t) - εTt - c → 0` and `r → 0` in
`C^∞`. Then for `s` large the `ξ`-part of `∂ₛW`, its projection
`π_W v = v - (dH(W) v / dH(W) W) W - λ₀(W)(v) R(W)` onto `ξ_W` along `W` and `R(W)`, vanishes
nowhere. -/
theorem xiPart_partialS_ne_zero_of_eigenTube {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (κ ε c s₀ : ℝ) (hκ : κ < 0)
    (v : ℝ → V n) (hv : IsXiLoop P v) (hv0 : ∀ t : ℝ, v t ≠ 0)
    (τ : ℝ × ℝ → ℝ) (r : ℝ × ℝ → V n) (W : ℝ × ℝ → V n)
    (hτ : TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c))
    (hr : TendstoZeroCInfty r)
    (hW : ∀ s ≥ s₀, ∀ t : ℝ, W (s, t) =
      proj H (P.x (τ (s, t)) + Real.exp (κ * s) • (v (τ (s, t) / P.T) + r (s, t)))) :
    ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      let w := W (s, t)
      let d := fderiv ℝ W (s, t) (1, 0)
      d - (fderiv ℝ H w d / fderiv ℝ H w w) • w - liouville w d • reeb H w ≠ 0 := by
  sorry

end FiniteEnergyPlane
