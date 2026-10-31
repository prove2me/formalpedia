-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_le_mul_norm_of_periodic
-- name    : FiniteEnergyPlane.exists_norm_le_mul_norm_of_periodic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T09:33:58.524254+00:00
-- url     : https://prove2.me/theorems/3ba825fa-3ece-4327-bce0-a1580e25d191
-- title:
--   Uniform linear bound for a periodic map vanishing on the zero section
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$ a real normed space, $T,r>0$, and let $\Phi:\mathbb{R}\times E\to F$ be $C^1$ on $\mathbb{R}\times B(0,r)$, $T$-periodic in its first variable there, with $\Phi(\varphi,0)=0$ for all $\varphi$. Then there is $L\ge0$ with $$\|\Phi(\varphi,v)\|\le L\|v\|\qquad\text{for all }\varphi\in\mathbb{R}\text{ and }\|v\|\le r/2.$$
--
--   This gives Lipschitz-type estimates near a periodic orbit that are uniform along the orbit.
--
--   **Formalization Note** Periodicity is assumed only for $\|v\|<r$; outside $\mathbb{R}\times B(0,r)$, $\Phi$ is arbitrary.
-- source:
--   Used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorems 2.10-2.11, and H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Mathlib

namespace FiniteEnergyPlane

open Metric

/-- A `C¹` map `Φ(φ, v)` on `ℝ × B(0, r)`, `T`-periodic in `φ` and vanishing on `v = 0`, is bounded
by a constant times `‖v‖` on `ℝ × B̄(0, r/2)`, uniformly in `φ`. -/
theorem exists_norm_le_mul_norm_of_periodic {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (T r : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (v : E), ‖v‖ < r → Φ (φ + T, v) = Φ (φ, v))
    (h0 : ∀ φ : ℝ, Φ (φ, 0) = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (φ : ℝ) (v : E), ‖v‖ ≤ r / 2 → ‖Φ (φ, v)‖ ≤ L * ‖v‖ := by
  sorry

end FiniteEnergyPlane
