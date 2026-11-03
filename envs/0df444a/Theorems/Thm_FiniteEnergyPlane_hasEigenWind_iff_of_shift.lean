-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasEigenWind_iff_of_shift
-- name    : FiniteEnergyPlane.hasEigenWind_iff_of_shift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:24:33.088542+00:00
-- url     : https://prove2.me/theorems/a6dd87e3-16fa-426c-8edc-bffd844900aa
-- title:
--   Eigenvector windings of the asymptotic operator do not depend on the starting point of the orbit
-- statement:
--   Let $P=(x,T)$ be a periodic Reeb orbit on a star-shaped level $S\subset\mathbb{R}^4$, $J$ a complex structure on $\xi$, $c\in\mathbb{R}$, and let $P'=(x',T)$ be the same orbit started at time $c$: $x'(\tau)=x(\tau+c)$. Then for every $\mu\in\mathbb{R}$ and $k\in\mathbb{Z}$, $\mu$ is an eigenvalue of the asymptotic operator $A_P$ all of whose eigenvectors have winding number $k$ in the global frame of $\xi$ if and only if the same holds for $A_{P'}$.
--
--   So the winding numbers $\alpha^\pm$ of a periodic orbit do not depend on its starting point.
--
--   **Formalization Note** The orbits are `ReebOrbit H` with `P'.T = P.T` and `P'.x τ = P.x (τ + c)`; the property is `HasEigenWind J P μ k`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Theorem 3.10; U. Hryniewicz, J. Symplectic Geom. 12 (2014), Remark 2.6 (auxiliary lemma)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The windings of the eigenvectors of the asymptotic operator do not depend on the starting
point of the periodic Reeb orbit: if `P'` is `P` started at time `c` (same period,
`x'(τ) = x(τ + c)`), then `μ` has eigenvector winding `k` for `P` if and only if it does
for `P'`. -/
theorem hasEigenWind_iff_of_shift {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1)
    (P P' : ReebOrbit H) (c : ℝ) (hT : P'.T = P.T) (hx : ∀ τ, P'.x τ = P.x (τ + c))
    (μ : ℝ) (k : ℤ) :
    HasEigenWind J P μ k ↔ HasEigenWind J P' μ k := by
  sorry

end FiniteEnergyPlane
