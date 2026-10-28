-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_blowup_points
-- name    : FiniteEnergyPlane.exists_blowup_points
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T17:56:16.675696+00:00
-- url     : https://prove2.me/theorems/156240f5-2fbd-4e61-a21e-c3c2ce338d8b
-- title:
--   Blow-up points with a doubling bound on shrinking discs
-- statement:
--   For each $k\in\mathbb N$ let $U_k\subseteq\mathbb C$ and let $g_k:\mathbb C\to[0,\infty)$ be continuous on $U_k$. Let $\rho>0$ and let $z_k\in\mathbb C$ satisfy $\overline B(z_k,\rho)\subseteq U_k$, $g_k(z_k)>0$ and $g_k(z_k)\to\infty$. Then there are points $\zeta_k\in\mathbb C$ and radii $\varepsilon_k>0$ such that
--   - $\varepsilon_k\to0$, $\ \varepsilon_k\,g_k(\zeta_k)\to\infty$ and $|z_k-\zeta_k|\to0$;
--   - $g_k(\zeta_k)>0$ and $\overline B(\zeta_k,\varepsilon_k)\subseteq U_k$;
--   - $g_k(y)\le 2\,g_k(\zeta_k)$ for every $y\in\overline B(\zeta_k,\varepsilon_k)$.
--
--   Near points where a sequence of functions blows up, there are nearby points where the function is controlled by twice its value on a disc whose radius, measured in units of $1/g_k(\zeta_k)$, tends to infinity.
--
--   **Formalization Note** The discs are closed balls `closedBall`. Continuity is `ContinuousOn (g k) (U k)`; nonnegativity is required at every point of $\mathbb C$.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, proof of Lemma 2.20, p. 12; H. Hofer, Invent. Math. 114 (1993), Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Blow-up points with doubling control. Let `g_k ≥ 0` be continuous on `U_k ⊆ ℂ`, and let
`z_k` be points with `B̄(z_k, ρ) ⊆ U_k` for a fixed `ρ > 0`, `g_k(z_k) > 0` and
`g_k(z_k) → ∞`. Then there are points `ζ_k` and radii `ε_k > 0` with `ε_k → 0`,
`ε_k g_k(ζ_k) → ∞`, `|z_k - ζ_k| → 0`, `g_k(ζ_k) > 0`, `B̄(ζ_k, ε_k) ⊆ U_k`, and
`g_k ≤ 2 g_k(ζ_k)` on `B̄(ζ_k, ε_k)`. -/
theorem exists_blowup_points (g : ℕ → ℂ → ℝ) (U : ℕ → Set ℂ) (z : ℕ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ∀ k, closedBall (z k) ρ ⊆ U k) (hg : ∀ k, ContinuousOn (g k) (U k))
    (hg0 : ∀ k w, 0 ≤ g k w) (hpos : ∀ k, 0 < g k (z k))
    (hblow : Tendsto (fun k => g k (z k)) atTop atTop) :
    ∃ ζ : ℕ → ℂ, ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun k => ε k * g k (ζ k)) atTop atTop ∧
      Tendsto (fun k => ‖z k - ζ k‖) atTop (𝓝 0) ∧ (∀ k, 0 < g k (ζ k)) ∧
      (∀ k, closedBall (ζ k) (ε k) ⊆ U k) ∧
      ∀ k, ∀ y ∈ closedBall (ζ k) (ε k), g k y ≤ 2 * g k (ζ k) := by
  sorry

end FiniteEnergyPlane
