-- Prove2me | Theorems.Thm_EthierKurtz_oblique_boundary_chart_local_inverse
-- name    : EthierKurtz.oblique_boundary_chart_local_inverse
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-01T22:52:16.290121+00:00
-- url     : https://prove2.me/theorems/9fc9e7dd-186b-4b24-9ce2-0e07deaf831a
-- title:
--   Quantitative local inverse of a boundary-flattening chart
-- statement:
--   Let $\Theta$ be a boundary-flattening chart at $x_0$ on $B(x_0,r_0)$ with the regularity of the statement ($\Theta$ strictly differentiable with derivative $D\Theta$, $D\Theta(x_0)=\mathrm{id}$, $\Theta(x_0)=0$, $\Theta, D\Theta$ Lipschitz with constant $K$, $D^2\Theta$ bounded and $\mu$-Hoelder). Then there are $0<r_1\le r_0$ and a map $\Lambda$ such that $$\tfrac12\|x-x'\|\le\|\Theta x-\Theta x'\|\le 2\|x-x'\|\quad(x,x'\in B(x_0,r_1)),$$ $\Lambda$ maps $\overline B(0,r_1/4)$ into $\overline B(x_0,r_1/2)$ with $\Theta\circ\Lambda=\mathrm{id}$ there, $\Lambda$ is $2$-Lipschitz on $\overline B(0,r_1/4)$, and $\Lambda(\Theta x)=x$ whenever $x\in B(x_0,r_1)$ and $\Theta x\in\overline B(0,r_1/4)$.
--
--   Role: provides the inverse chart used to transport the boundary problem to the half-space and back.
-- source:
--   W. Rudin, Principles of Mathematical Analysis, 3rd ed., McGraw-Hill, 1976, Theorem 9.24 (inverse function theorem) and its proof (contraction estimate on a ball where $\|D\Theta-I\|\le 1/2$); applied to the boundary-flattening maps of D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.2; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369)

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
open MeasureTheory Real Set Filter
open scoped Topology
open scoped BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_boundary_chart_local_inverse (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d)) (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (D2Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hchart : 0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) ∧
        (∀ x ∈ Metric.ball x0 r0,
          (x ∈ Ω ↔ 0 < inner ℝ (Θ x) e) ∧ (x ∈ frontier Ω ↔ inner ℝ (Θ x) e = 0)) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ frontier Ω, ∃ κ : ℝ, 0 < κ ∧ DΘ x (c x) = κ • (b - e)) ∧
        0 ≤ K ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖Θ x - Θ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖DΘ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖DΘ x - DΘ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖D2Θ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ)) :
    ∃ r1 : ℝ, 0 < r1 ∧ r1 ≤ r0 ∧ ∃ Λ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x ∈ Metric.ball x0 r1, ∀ x' ∈ Metric.ball x0 r1,
        ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖ ∧ ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖) ∧
      (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4), Λ z ∈ Metric.closedBall x0 (r1 / 2) ∧ Θ (Λ z) = z) ∧
      (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4), ∀ z' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4),
        ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) ∧
      (∀ x ∈ Metric.ball x0 r1, Θ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4) → Λ (Θ x) = x) := by sorry

end EthierKurtz
