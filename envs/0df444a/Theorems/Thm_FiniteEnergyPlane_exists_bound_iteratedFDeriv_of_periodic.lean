-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_bound_iteratedFDeriv_of_periodic
-- name    : FiniteEnergyPlane.exists_bound_iteratedFDeriv_of_periodic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T10:21:32.520072+00:00
-- url     : https://prove2.me/theorems/f8c6d902-0741-419a-a3d8-6450452b6ca7
-- title:
--   Uniform bounds on all derivatives of a smooth periodic map on a tube
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$ a real normed space, $T,r>0$, and let $\Phi:\mathbb{R}\times E\to F$ be $C^\infty$ on $\mathbb{R}\times B(0,r)$ and $T$-periodic in its first variable there: $\Phi(\varphi+T,v)=\Phi(\varphi,v)$ for $\|v\|<r$. Then for every $n\ge0$ there is $C$ with
--   $$\|D^n\Phi(\varphi,v)\|\le C\qquad\text{for all }\varphi\in\mathbb{R},\ \|v\|\le r/2.$$
--
--   So every derivative of such a map is uniformly bounded on the closed half-radius tube $\mathbb{R}\times\overline{B}(0,r/2)$, although $\mathbb{R}$ is not compact. This is used to control derivatives of compositions with maps defined along a periodic orbit.
--
--   **Formalization Note** $D^n\Phi$ is the full Fréchet derivative `iteratedFDeriv ℝ n Φ` of $\Phi$ on $\mathbb{R}\times E$; smoothness and periodicity are only assumed on $\mathbb{R}\times B(0,r)$.
-- source:
--   Used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorems 2.10-2.11, and H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Mathlib

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- A map `Φ(φ, v)` that is smooth on `ℝ × B(0, r)` and `T`-periodic in `φ` has each derivative
`D^n Φ` bounded on `ℝ × closedBall(0, r/2)`. -/
theorem exists_bound_iteratedFDeriv_of_periodic {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v)) (n : ℕ) :
    ∃ C : ℝ, ∀ (φ : ℝ) (v : E), ‖v‖ ≤ r / 2 → ‖iteratedFDeriv ℝ n Φ (φ, v)‖ ≤ C := by
  sorry

end FiniteEnergyPlane
