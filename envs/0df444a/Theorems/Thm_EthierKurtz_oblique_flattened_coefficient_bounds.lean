-- Prove2me | Theorems.Thm_EthierKurtz_oblique_flattened_coefficient_bounds
-- name    : EthierKurtz.oblique_flattened_coefficient_bounds
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-01T22:53:00.06271+00:00
-- url     : https://prove2.me/theorems/a848d993-1a6c-41f7-84b8-c3608d3611a2
-- title:
--   Bounds for the coefficients of the operator transformed by a boundary-flattening chart
-- statement:
--   Let $\Theta$ have $D\Theta,D^2\Theta$ bounded by $K$ on a set $S$, with $\Theta,D\Theta$ $K$-Lipschitz and $D^2\Theta$ $\mu$-Hoelder with constant $K$ ($0\le\mu\le1$), $D\Theta(x_0)=\mathrm{id}$, and let $\Lambda$ be $2$-Lipschitz from a set $Z
--   i0$ of radius $\le\rho$ into $S$ with $\Lambda(0)=x_0$. If $a,b$ are bounded by $K_a$ and $\mu$-Hoelder with constant $K_a$ on $S$, then the transformed coefficients $$\tilde a_{kl}(z)=\tfrac12\Big(\sum_{i,j}a_{ij}(\Lambda z)\,\partial_i\Theta_k(\Lambda z)\,\partial_j\Theta_l(\Lambda z)-a_{kl}(x_0)\Big),\qquad \tilde b_k(z)=\tfrac12\sum_{i,j}a_{ij}(\Lambda z)\,\partial_{ij}\Theta_k(\Lambda z)+(D\Theta(\Lambda z)\,b(\Lambda z))_k$$ satisfy $|\tilde a_{kl}|\le K_aK^2(2\rho)^\mu+K_a(K+1)K\rho$, $|\tilde a_{kl}(z)-\tilde a_{kl}(z')|\le K_aK^2\|z-z'\|^\mu+2K_aK^2\|z-z'\|$, $|\tilde b_k|\le 2K_aK$ and $|\tilde b_k(z)-\tilde b_k(z')|\le 4K_aK\|z-z'\|^\mu+2K_aK\|z-z'\|$.
--
--   Role: shows that after flattening, the perturbation of the frozen principal part is small on small balls and the lower-order coefficients stay Hoelder, as the half-space model requires.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.2 (transformation of the operator under the boundary-flattening map and the resulting coefficient estimates), used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369)

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
open MeasureTheory Real Set Filter
open scoped Topology
open scoped BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_flattened_coefficient_bounds (d : ℕ) (S Z : Set (EuclideanSpace ℝ (Fin d))) (μ K ρ Ka : ℝ) (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (D2Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hC : 0 ≤ K ∧ (∀ x ∈ S, ∀ y ∈ S, ‖Θ x - Θ y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖DΘ x‖ ≤ K) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖DΘ x - DΘ y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖D2Θ x‖ ≤ K) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ))
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ S)
    (hD0 : DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) (Λ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΛS : ∀ z ∈ Z, Λ z ∈ S)
    (h0Z : (0 : EuclideanSpace ℝ (Fin d)) ∈ Z) (hΛ0 : Λ 0 = x0) (hΛl : ∀ z ∈ Z, ∀ z' ∈ Z, ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖)
    (hρ : ∀ z ∈ Z, ‖z‖ ≤ ρ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bb : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hab : ∀ x ∈ S, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka)
    (hah : ∀ x ∈ S, ∀ x' ∈ S, ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧
      ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) :
    (∀ z ∈ Z, ∀ k l, |(1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (DΘ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z)) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l)| ≤
      Ka * K ^ 2 * (2 * ρ) ^ μ + Ka * (K + 1) * K * ρ) ∧
    (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k l, |(1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (DΘ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z)) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l) - (1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z')) i j * (DΘ (Λ z')) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z')) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l)| ≤
      Ka * K ^ 2 * ‖z - z'‖ ^ μ + 2 * Ka * K ^ 2 * ‖z - z'‖) ∧
    (∀ z ∈ Z, ∀ k, |((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (D2Θ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z)) (bb (Λ z)) k)| ≤ 2 * Ka * K) ∧
    (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k, |((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (D2Θ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z)) (bb (Λ z)) k) -
      ((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z')) i j * (D2Θ (Λ z')) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z')) (bb (Λ z')) k)| ≤
      4 * Ka * K * ‖z - z'‖ ^ μ + 2 * Ka * K * ‖z - z'‖) := by sorry

end EthierKurtz
