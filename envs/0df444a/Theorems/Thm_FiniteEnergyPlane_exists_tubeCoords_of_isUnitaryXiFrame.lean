-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tubeCoords_of_isUnitaryXiFrame
-- name    : FiniteEnergyPlane.exists_tubeCoords_of_isUnitaryXiFrame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T15:49:16.351611+00:00
-- url     : https://prove2.me/theorems/52ca82cd-6143-40be-a3ed-83768468ed70
-- title:
--   Quantitative tube coordinates near a periodic Reeb orbit in a unitary frame
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be strictly star-shaped, $J$ a complex structure on $\xi$, $P = (x, T)$ a periodic Reeb orbit and $Z$ a unitary frame of $\xi$ along $P$. Then there are $r, \delta > 0$, $K \ge 0$ and maps $\theta, \rho : \mathbb{R} \times \mathbb{R}^4 \to \mathbb{R}$ and $A : \mathbb{R} \times \mathbb{R}^4 \to \mathbb{R}^2$ such that, for all $\varphi \in \mathbb{R}$ and $|u| < r$ (writing $\theta = \theta(\varphi, u)$, $A = A(\varphi, u)$, $\rho = \rho(\varphi, u)$):
--   - $\theta$ and $A$ are continuous on $\mathbb{R} \times B(0, r)$;
--   - $\rho > 0$ and $\rho\,(x(\varphi) + u) = x(\varphi + \theta) + Z((\varphi + \theta)/T)\,A$;
--   - if $x(\varphi) + u \in S$, then $|x(\varphi) + u - x(\varphi + \theta)| \le K|A|$ and $|\rho - 1| \le K|A|^2$;
--   - if $u = Z(\varphi/T)\,b$, then $\theta = 0$ and $A = b$;
--   - $|\theta(\varphi, u') - \theta(\varphi, u)| \le K|u' - u|$ and $|A(\varphi, u') - A(\varphi, u)| \le K|u' - u|$ whenever $|u' - u| \le \delta$.
--
--   In particular, every point $q = x(\varphi) + u \in S$ near $x(\mathbb{R})$ satisfies $q = \mathrm{proj}(x(\varphi + \theta) + Z((\varphi + \theta)/T)\,A)$.
--
--   Role: tube coordinates $(\tau, a)$, with $q = \mathrm{proj}(x(\tau) + Z(\tau/T)\,a)$, depending continuously and locally Lipschitz on the point, exact on the frame directions, and with the radial factor $\rho$ equal to $1$ to second order on $S$.
--
--   Formalization Note: $\theta$ is the phase shift, so the base point is $x(\varphi + \theta(\varphi, u))$. Points are written $x(\varphi) + u$ relative to an arbitrary base phase $\varphi$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2; H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), Section 5

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric Set

/-- Tube coordinates near a periodic Reeb orbit `P = (x, T)` in a unitary frame `Z` of `ξ`.
There are `r, δ > 0`, `K ≥ 0` and maps `θ, ρ : ℝ × V 1 → ℝ`, `A : ℝ × V 1 → ℝ²` with the
following properties, for `‖u‖ < r`.
* `θ` and `A` are continuous on `ℝ × ball 0 r`.
* `ρ(φ, u) > 0` and `ρ(φ, u) (x(φ) + u) = x(φ + θ) + Z((φ + θ)/T) A`, evaluated at `(φ, u)`.
* If `x(φ) + u ∈ S`, then `‖x(φ) + u - x(φ + θ)‖ ≤ K ‖A‖` and `|ρ - 1| ≤ K ‖A‖²`.
* On the frame directions `u = Z(φ/T) b`: `θ = 0` and `A = b`.
* `θ(φ, ·)` and `A(φ, ·)` are `K`-Lipschitz for increments of size at most `δ`.

Formalization Note: `θ` is the phase shift, so the base point is `x(φ + θ(φ, u))`. -/
theorem exists_tubeCoords_of_isUnitaryXiFrame (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hZ : IsUnitaryXiFrame J P Z) :
    ∃ r > 0, ∃ K, 0 ≤ K ∧ ∃ δ > 0, ∃ (θ : ℝ × V 1 → ℝ) (A : ℝ × V 1 → CauchyRiemannIndex.Vec 1)
      (ρ : ℝ × V 1 → ℝ),
      ContinuousOn θ (univ ×ˢ ball (0 : V 1) r) ∧ ContinuousOn A (univ ×ˢ ball (0 : V 1) r) ∧
      (∀ φ u, ‖u‖ < r → 0 < ρ (φ, u) ∧
        ρ (φ, u) • (P.x φ + u) = P.x (φ + θ (φ, u)) + Z ((φ + θ (φ, u)) / P.T) (A (φ, u))) ∧
      (∀ φ u, ‖u‖ < r → H (P.x φ + u) = 1 →
        ‖P.x φ + u - P.x (φ + θ (φ, u))‖ ≤ K * ‖A (φ, u)‖ ∧ |ρ (φ, u) - 1| ≤ K * ‖A (φ, u)‖ ^ 2) ∧
      (∀ φ b, ‖Z (φ / P.T) b‖ < r → θ (φ, Z (φ / P.T) b) = 0 ∧ A (φ, Z (φ / P.T) b) = b) ∧
      (∀ φ (u u' : V 1), ‖u‖ < r → ‖u' - u‖ ≤ δ →
        |θ (φ, u') - θ (φ, u)| ≤ K * ‖u' - u‖ ∧ ‖A (φ, u') - A (φ, u)‖ ≤ K * ‖u' - u‖) := by
  sorry

end FiniteEnergyPlane
