-- Prove2me | Theorems.Thm_EthierKurtz_oblique_variable_coeff_perturbation
-- name    : EthierKurtz.oblique_variable_coeff_perturbation
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:48:16.509245+00:00
-- url     : https://prove2.me/theorems/1f870cb9-1498-423b-b5af-fa26274cb344
-- title:
--   Variable-coefficient perturbation of the half-space oblique model
-- statement:
--   If the constant-coefficient half-space oblique problem is solvable with the Schauder bounds of the statement, then so is the variable-coefficient problem whose coefficients are $\mu$-Hoelder and $\delta$-close to the constant ones, for $\lambda$ large: $$\lambda u-\sum a_{ij}\partial_{ij}u=h .$$
--
--   Role: the freezing-of-coefficients step.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7, proof of Theorem 6.30 (freezing the coefficients) and Section 6.1; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem oblique_variable_coeff_perturbation (d : ℕ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hHM : ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ lam : ℝ, 0 < lam → ∀ h : EuclideanSpace ℝ (Fin d) → ℝ,
        (∃ Hh : ℝ, ∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
        (∃ M0 : ℝ, ∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |h y| ≤ M0) →
        ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
          (∀ x : EuclideanSpace ℝ (Fin d), 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e →
            lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
              = h x) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
          ∀ M0 Hh : ℝ, 0 ≤ M0 → 0 ≤ Hh → (∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |h y| ≤ M0) →
            (∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
          (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∀ v w : EuclideanSpace ℝ (Fin d),
            |u x| ≤ C * M0 * (1 / lam) ∧
            |u1 x v| ≤ C * M0 * (1 / lam) ^ (1 / 2 : ℝ) * ‖v‖ ∧
            |u2 x v w| ≤ C * Hh * (1 / lam) ^ (μ / 2) * ‖v‖ * ‖w‖) ∧
          (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : EuclideanSpace ℝ (Fin d),
            |u x - u x'| ≤ C * M0 * (1 / lam) ^ (1 - μ / 2) * ‖x - x'‖ ^ μ ∧
            |u1 x v - u1 x' v| ≤ C * M0 * (1 / lam) ^ ((1 - μ) / 2) * ‖x - x'‖ ^ μ * ‖v‖ ∧
            |u2 x v w - u2 x' v w| ≤ C * Hh * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖)) :
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
            |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖) := by sorry

end EthierKurtz
