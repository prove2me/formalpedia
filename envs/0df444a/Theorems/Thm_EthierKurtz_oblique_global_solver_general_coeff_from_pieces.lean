-- Prove2me | Theorems.Thm_EthierKurtz_oblique_global_solver_general_coeff_from_pieces
-- name    : EthierKurtz.oblique_global_solver_general_coeff_from_pieces
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T00:13:46.731798+00:00
-- url     : https://prove2.me/theorems/115dc1a0-7a9c-433d-8ba9-03633eaddad3
-- title:
--   Global oblique solver for variable coefficients from local solution pieces
-- statement:
--   Let $\Omega$ be bounded and open, $0<\mu<1$, and suppose every point of $\overline\Omega$ has local cut-off solution pieces for $\lambda u-\tfrac12a:D^2u-\nabla u\cdot b=g$, $\nabla u\cdot c=0$ with uniform Schauder bounds and local $\mu$-Hoelder bounds on $a,b$ (the hypothesis hpiece). Then there is $\lambda_1\ge1$ such that for every $\lambda\ge\lambda_1$ and every bounded $\mu$-Hoelder $g$ on $\overline\Omega$ there is $u\in C^2(\Omega)$ with $u,Du,D^2u$ bounded and $\mu$-Hoelder on $\overline\Omega$, $$\lambda u-\tfrac12 a:D^2u-\nabla u\cdot b=g \text{ on }\overline\Omega,\qquad \nabla u\cdot c=0 \text{ on }\partial\Omega.$$
--
--   Role: the patching step (partition of unity, commutator estimate, Neumann-series inversion).
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7, proof of Theorem 6.31 (patching of local solutions) and Section 6.3; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369)

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
open MeasureTheory Real Set Filter
open scoped Topology
open scoped BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_global_solver_general_coeff_from_pieces (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bb : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hpiece : ∀ x0 ∈ closure Ω, ∃ (ρ Z τ : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (χ1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (χ2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (lam0 C Ka : ℝ),
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
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)) ∧ 0 ≤ Ka ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ)) :
    (∃ lam1 : ℝ, 1 ≤ lam1 ∧ ∀ lam : ℝ, lam1 ≤ lam → ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ),
      (0 ≤ M ∧ 0 ≤ H ∧ (∀ x ∈ closure Ω, |g x| ≤ M) ∧
        ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
      ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
        (∀ x ∈ Ω, HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
        (∀ x ∈ frontier Ω, u1 x (c x) = 0) ∧
        (∀ x ∈ closure Ω, lam * u x -
          (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
            - u1 x (bb x) = g x) ∧
        (∃ B : ℝ, ∀ x ∈ closure Ω, |u x| ≤ B ∧ ‖u1 x‖ ≤ B ∧ ‖u2 x‖ ≤ B) ∧
        (∃ B : ℝ, ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |u x - u y| ≤ B * ‖x - y‖ ^ μ ∧
          ‖u1 x - u1 y‖ ≤ B * ‖x - y‖ ^ μ ∧ ‖u2 x - u2 y‖ ≤ B * ‖x - y‖ ^ μ)) := by sorry

end EthierKurtz
