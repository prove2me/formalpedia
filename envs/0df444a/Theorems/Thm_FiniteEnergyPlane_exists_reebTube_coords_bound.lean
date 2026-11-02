-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_reebTube_coords_bound
-- name    : FiniteEnergyPlane.exists_reebTube_coords_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T09:05:27.4291+00:00
-- url     : https://prove2.me/theorems/576ef42a-a95c-48ad-a56e-8a228f4b0ae9
-- title:
--   Tube coordinates near a periodic Reeb orbit with two-sided bounds
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $P=(x,T)$ a periodic Reeb orbit on $S$, $\varepsilon=\pm1$, $c\in\mathbb{R}$, and let $w:\mathbb{R}^2\to\mathbb{R}^{2n+2}$ take values in $S$ for $s>s_0$, be $1$-periodic in $t$, and satisfy $w(s,t)-x(\varepsilon Tt+c)\to0$ in $C^\infty$, uniformly in $t$, as $s\to+\infty$. Then there are $\tau:\mathbb{R}^2\to\mathbb{R}$, $h:\mathbb{R}^2\to\mathbb{R}^{2n+2}$ and constants $s_1,K$ with $\tau(s,t)-\varepsilon Tt-c\to0$ and $h\to0$ in $C^\infty$, such that for $s\ge s_1$:
--
--   - $\tau(s,t+1)=\tau(s,t)+\varepsilon T$, $h(s,t+1)=h(s,t)$, $h(s,t)\in\xi_{x(\tau(s,t))}$ and $w(s,t)=\mathrm{proj}\big(x(\tau(s,t))+h(s,t)\big)$;
--   - $\|w-x(\tau)\|\le K\|h\|$ and $\|w-x(\varepsilon Tt+c)\|\le K\big(\|h\|+|\tau-\varepsilon Tt-c|\big)$;
--   - $\|h\|+|\tau-\varepsilon Tt-c|\le K\,\|w-x(\varepsilon Tt+c)\|$.
--
--   So the tube coordinates $(\tau,h)$ of a map close to a trivial cylinder are comparable, in both directions, to its distance from that cylinder.
--
--   **Formalization Note** `TendstoZeroCInfty f` means: $f$ is smooth on some $(s_0,\infty)\times\mathbb{R}$ and every derivative $D^mf(s,t)$ tends to $0$ uniformly in $t$ as $s\to+\infty$. $\mathrm{proj}$ is the radial projection `proj H` onto $S$ and $\xi_y$ is `IsInXi H y`.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 and Lemma 2.12; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Tube coordinates around a periodic Reeb orbit `P = (x, T)` on a strictly star-shaped level `S`,
with two-sided bounds. Let `w(s, t) ∈ S` (for `s > s₀`) be `1`-periodic in `t` with
`w(s, t) - x(εTt + c) → 0` in `C^∞`. Then for `s ≥ s₁` the map `w` is written as
`w = proj H (x(τ) + h)` with `h ∈ ξ_{x(τ)}`, where `τ(s, t + 1) = τ(s, t) + εT`, `h` is
`1`-periodic, `τ(s, t) - εTt - c → 0` and `h → 0` in `C^∞`; moreover
`‖w - x(τ)‖ ≤ K ‖h‖`, `‖w - x(εTt + c)‖ ≤ K (‖h‖ + |τ - εTt - c|)` and, conversely,
`‖h‖ + |τ - εTt - c| ≤ K ‖w - x(εTt + c)‖`. -/
theorem exists_reebTube_coords_bound {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c : ℝ) (w : ℝ × ℝ → V n) (s₀ : ℝ)
    (hwS : ∀ s > s₀, ∀ t : ℝ, H (w (s, t)) = 1)
    (hwper : ∀ s t : ℝ, w (s, t + 1) = w (s, t))
    (hw : TendstoZeroCInfty (fun p : ℝ × ℝ => w p - P.x (ε * P.T * p.2 + c))) :
    ∃ (τ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → V n) (s₁ K : ℝ),
      TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) ∧ TendstoZeroCInfty h ∧
      ∀ s ≥ s₁, ∀ t : ℝ,
        τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧ w (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) ∧
        ‖w (s, t) - P.x (τ (s, t))‖ ≤ K * ‖h (s, t)‖ ∧
        ‖w (s, t) - P.x (ε * P.T * t + c)‖ ≤ K * (‖h (s, t)‖ + |τ (s, t) - ε * P.T * t - c|) ∧
        ‖h (s, t)‖ + |τ (s, t) - ε * P.T * t - c| ≤ K * ‖w (s, t) - P.x (ε * P.T * t + c)‖ := by
  sorry

end FiniteEnergyPlane
