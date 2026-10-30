-- Prove2me | Theorems.Thm_EthierKurtz_oblique_global_solver_from_pieces
-- name    : EthierKurtz.oblique_global_solver_from_pieces
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:03:37.121786+00:00
-- url     : https://prove2.me/theorems/3e5109a8-b053-4fd1-b564-ecdab8d0d809
-- title:
--   Global oblique solver from a finite family of local solution pieces
-- statement:
--   Let $\Omega$ be bounded and open, $0<\mu<1$, and suppose every point of $\overline\Omega$ has a neighbourhood with local cut-off solution operators for $\lambda u-\frac12\Delta u=h$, $c\cdot\nabla u=0$, with uniform Schauder bounds (the hypotheses of the statement). Then there is $\lambda_0>0$ such that the global problem is solvable in `obliqueDiffusionGraph` for every bounded $\mu$-Hoelder $h$: $$\lambda_0u-\tfrac12\Delta u=h .$$
--
--   Role: the patching step (partition of unity and Neumann-series inversion of the commutator error).
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7, proof of Theorem 6.31 (patching of local solutions), and Section 6.3 (method of continuity); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
open MeasureTheory Real Set Filter
open scoped Topology
open EthierKurtz
open scoped BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_global_solver_from_pieces (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hpiece : ∀ x0 ∈ closure Ω, ∃ (ρ Z τ : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (χ1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (χ2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (lam0 C : ℝ),
      (0 < ρ ∧
        0 < τ ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt χ (χ1 x) x ∧ HasFDerivAt χ1 (χ2 x) x) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, χ1 x (c x) = 0) ∧
        (∀ y ∈ Metric.ball x0 ρ, ρ / 2 ≤ ‖y - x0‖ → χ y = 0 ∧ χ1 y = 0 ∧ χ2 y = 0) ∧
        (∀ y ∈ Metric.ball x0 τ, χ y = 1) ∧
        (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
        0 ≤ Z ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ x - χ y‖ ≤ Z * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ1 x‖ ≤ Z) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ1 x - χ1 y‖ ≤ Z * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ2 x‖ ≤ Z) ∧
        (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ y ∈ Metric.ball x0 ρ ∩ closure Ω, ‖χ2 x - χ2 y‖ ≤ Z * ‖x - y‖ ^ μ)) ∧ 1 ≤ lam0 ∧ 0 ≤ C ∧
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
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ))) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ0.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
          lam₀ • fg.1 - fg.2 = h := by sorry

end EthierKurtz
