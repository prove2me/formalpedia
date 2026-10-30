-- Prove2me | Theorems.Thm_EthierKurtz_oblique_boundary_local_solver
-- name    : EthierKurtz.oblique_boundary_local_solver
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T21:56:08.595151+00:00
-- url     : https://prove2.me/theorems/8909aa83-a81a-4b60-8887-6cfa60891288
-- title:
--   Local oblique solver in a flattened boundary chart
-- statement:
--   Given a $C^{2,\mu}$ flattening chart of $\partial\Omega$ at a boundary point and the variable-coefficient half-space solvability of the statement, $0<\mu<1$, there are $\rho,\lambda_0,C>0$ and a local solver of $$\lambda u-\tfrac12\Delta u=h\text{ near }x_0,\qquad c\cdot\nabla u=0\text{ on }\partial\Omega$$ with Schauder bounds.
--
--   Role: transfers the half-space theory to a boundary neighbourhood through the chart.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7, Lemma 6.29 and the flattening argument of Theorem 6.30; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem oblique_boundary_local_solver (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hV : ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
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
        lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
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
    (hch : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d))
        (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (D2Θ : EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
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
    ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d))
        (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (D2Θ : EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        (0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
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
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ)) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧
      (∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : EuclideanSpace ℝ (Fin d) → ℝ) (W1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (W2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x) ∧
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
