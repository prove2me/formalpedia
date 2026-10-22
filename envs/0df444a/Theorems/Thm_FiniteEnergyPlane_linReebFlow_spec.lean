-- Prove2me | Theorems.Thm_FiniteEnergyPlane_linReebFlow_spec
-- name    : FiniteEnergyPlane.linReebFlow_spec
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:40:46.079556+00:00
-- url     : https://prove2.me/theorems/89c58455-2ac5-4e2d-b5b7-e77c55b4d288
-- title:
--   The linearized Reeb flow along a periodic orbit
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $P=(x,T)$ a periodic Reeb orbit on $S$. There is exactly one linearized Reeb flow $\Phi$ along $P$, and for every $\tau\in\mathbb{R}$: $\Phi(\tau)$ maps $\xi_{x(0)}$ into $\xi_{x(\tau)}$, $\omega_0(\Phi(\tau)v,\Phi(\tau)w)=\omega_0(v,w)$ for $v,w\in\xi_{x(0)}$, and $\Phi(\tau+T)=\Phi(\tau)\circ\Phi(T)$.
--
--   **Formalization Note** The flow is `IsLinReebFlow P Φ` with `Φ : ℝ → V n →L[ℝ] V n`, with the derivative of `reeb H` on $V$; the first claim is `∃!`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Section 3.1; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The linearized Reeb flow along a periodic Reeb orbit `P = (x, T)` exists and is unique. It
maps `ξ_{x(0)}` into `ξ_{x(τ)}`, preserves `ω₀` on `ξ_{x(0)}`, and satisfies
`Φ(τ + T) = Φ(τ) ∘ Φ(T)`. -/
theorem linReebFlow_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) :
    (∃! Φ : ℝ → V n →L[ℝ] V n, IsLinReebFlow P Φ) ∧
      ∀ Φ : ℝ → V n →L[ℝ] V n, IsLinReebFlow P Φ →
        (∀ τ : ℝ, ∀ v w : V n, IsInXi H (P.x 0) v → IsInXi H (P.x 0) w →
          IsInXi H (P.x τ) (Φ τ v) ∧ omega0 (Φ τ v) (Φ τ w) = omega0 v w) ∧
        ∀ τ : ℝ, Φ (τ + P.T) = (Φ τ).comp (Φ P.T) := by
  sorry

end FiniteEnergyPlane
