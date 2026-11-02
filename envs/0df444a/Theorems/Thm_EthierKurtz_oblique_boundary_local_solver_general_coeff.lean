-- Prove2me | Theorems.Thm_EthierKurtz_oblique_boundary_local_solver_general_coeff
-- name    : EthierKurtz.oblique_boundary_local_solver_general_coeff
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-01T22:53:26.740242+00:00
-- url     : https://prove2.me/theorems/81ba06f0-2281-4b93-97cf-fea9c8550e02
-- title:
--   Boundary local solver for the oblique problem with variable coefficients after flattening
-- statement:
--   Assume the half-space model with general constant principal part (hypothesis hV), a boundary-flattening chart $\Theta$ at $x_0\in\partial\Omega$ on $B(x_0,r_0)$ carrying the oblique field $c$ to a positive multiple of $b-e$ (hypothesis hchart), a quantitative local inverse $\Lambda$ of $\Theta$ (hypothesis hinv), the transformed-coefficient bounds (hypothesis hcoef), coefficients $a,b$ bounded by $K_a$ and $\mu$-Hoelder on $B(x_0,r_0)\cap\overline\Omega$, and $a(x_0)$ positive definite. Then there are $0<\rho\le r_0$, $\lambda_0\ge1$, $C\ge0$ such that for every $\lambda\ge\lambda_0$ and every bounded $\mu$-Hoelder $g$ there is $W$, $C^2$ on $B(x_0,\rho)\cap\Omega$, with $$\lambda W-\tfrac12\sum_{i,j}a_{ij}\,\partial_{ij}W-
--   abla W\cdot b=g \text{ on } B(x_0,\rho)\cap\overline\Omega,\qquad
--   abla W\cdot c=0 \text{ on } B(x_0,\rho)\cap\partial\Omega,$$ and the weighted Schauder bounds of the statement.
--
--   Role: the boundary case of the local pieces: the problem is pulled back to the half-space, solved there by the model with a small perturbation of the frozen principal part, and pushed forward by the chart.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7, proof of Theorem 6.31 (local solvability near boundary points after flattening, perturbation of frozen coefficients, using Lemma 6.29), used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369)

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
open MeasureTheory Real Set Filter
open scoped Topology
open scoped BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_boundary_local_solver_general_coeff (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hV : ∀ A0 : Matrix (Fin d) (Fin d) ℝ, A0.PosDef →
  ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
  ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
  ∀ (α : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ) (β : EuclideanSpace ℝ (Fin d) → Fin d → ℝ),
    (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
    (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
    (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
    (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |g y| ≤ M) →
    (∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
    ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x : EuclideanSpace ℝ (Fin d), 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e →
        lam * u x - (1 / 2 : ℝ) * ∑ i, ∑ j, A0 i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
        |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
      (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖))
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
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ))
    (hinv : ∃ r1 : ℝ, 0 < r1 ∧ r1 ≤ r0 ∧ ∃ Λ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        (∀ x ∈ Metric.ball x0 r1, ∀ x' ∈ Metric.ball x0 r1,
          ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖ ∧ ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖) ∧
        (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4), Λ z ∈ Metric.closedBall x0 (r1 / 2) ∧ Θ (Λ z) = z) ∧
        (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4), ∀ z' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4),
          ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) ∧
        (∀ x ∈ Metric.ball x0 r1, Θ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4) → Λ (Θ x) = x))
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bb : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Ka : ℝ)
    (hab : ∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka)
    (hah : ∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ x' ∈ Metric.ball x0 r0 ∩ closure Ω,
      ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ)
    (hcoef : ∀ (Z : Set (EuclideanSpace ℝ (Fin d))) (Λ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (ρ : ℝ), (∀ z ∈ Z, Λ z ∈ Metric.ball x0 r0 ∩ closure Ω) →
      (0 : EuclideanSpace ℝ (Fin d)) ∈ Z → Λ 0 = x0 → (∀ z ∈ Z, ∀ z' ∈ Z, ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) → (∀ z ∈ Z, ‖z‖ ≤ ρ) →
      (∀ z ∈ Z, ∀ k l, |(1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (DΘ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z)) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l)| ≤
        Ka * K ^ 2 * (2 * ρ) ^ μ + Ka * (K + 1) * K * ρ) ∧
      (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k l, |(1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (DΘ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z)) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l) - (1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z')) i j * (DΘ (Λ z')) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z')) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l)| ≤
        Ka * K ^ 2 * ‖z - z'‖ ^ μ + 2 * Ka * K ^ 2 * ‖z - z'‖) ∧
      (∀ z ∈ Z, ∀ k, |((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (D2Θ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z)) (bb (Λ z)) k)| ≤ 2 * Ka * K) ∧
      (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k, |((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (D2Θ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z)) (bb (Λ z)) k) -
        ((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z')) i j * (D2Θ (Λ z')) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z')) (bb (Λ z')) k)| ≤
        4 * Ka * K * ‖z - z'‖ ^ μ + 2 * Ka * K * ‖z - z'‖))
    (hpd : (a x0).PosDef) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r0 ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧
      (∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : EuclideanSpace ℝ (Fin d) → ℝ) (W1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (W2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - W1 x (bb x) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)) := by sorry

end EthierKurtz
