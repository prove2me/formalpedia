-- Prove2me | Theorems.Thm_EthierKurtz_oblique_halfspace_kernel_hypotheses
-- name    : EthierKurtz.oblique_halfspace_kernel_hypotheses
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:37:40.104982+00:00
-- url     : https://prove2.me/theorems/43232f28-2832-470b-88c6-6935756e0822
-- title:
--   Gaussian kernel hypotheses for the half-space oblique kernel
-- statement:
--   For every unit $e$ and $b$ with $\langle b,e\rangle=0$ the explicit kernel $$K=w_K(x,y)+w_K(x,R_ey)-2\int_0^\infty \partial_bG\big(x-R_ey+s(e-b)\big)ds$$ on the half-space $\{\langle y,e\rangle\ge0\}$ satisfies the Gaussian kernel hypotheses of the statement and the oblique boundary condition $(b-e)\cdot\nabla_x u=0$.
--
--   Role: provides the explicit half-space kernel.
-- source:
--   A. Friedman, Partial Differential Equations of Parabolic Type, Prentice-Hall, 1964, Chapter 1, Sections 2-4 (Gaussian kernel, heat potentials and their derivative estimates) and Chapter 5, Section 2 (oblique derivative problem in a half-space); D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7, Lemma 6.29; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem oblique_halfspace_kernel_hypotheses :
    ∀ (d : ℕ),
      letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
      letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
      letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
      letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
      letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
      letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
      letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
      letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
      letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
      letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup;
      letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace;
      letI : AddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup;
      letI : Module ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := ContinuousLinearMap.module;
        ∀ (e b : EuclideanSpace ℝ (Fin d)), ‖e‖ = 1 → inner ℝ b e = 0 →
        ∃ (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
          (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
          (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
          (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
          (A c : ℝ),
        (0 ≤ A ∧ 0 < c ∧ MeasurableSet ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧ Convex ℝ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧
          (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧
          (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧
          (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧
          (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), |K t x y| ≤ A * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
          (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
          (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
          (∀ t : ℝ, 0 < t → ∀ x ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), ∀ v w z : EuclideanSpace ℝ (Fin d),
            |K3 t x y v w z| ≤ A * t ^ (-(3 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t))) * ‖v‖ * ‖w‖ * ‖z‖) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K p.1 x p.2)) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K1 p.1 x p.2)) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K2 p.1 x p.2)) ∧
          (∀ x v w z : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K3 p.1 x p.2 v w z)) ∧
          (∀ t : ℝ, 0 < t → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.IntegrableOn F ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}) ∧
            ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧
              ∀ v w z : EuclideanSpace ℝ (Fin d), |K3 t x y v w z| ≤ F y * ‖v‖ * ‖w‖ * ‖z‖) ∧
          (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasDerivAt (fun t => K t x y)
            ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
          (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), ∫ y in ({y : EuclideanSpace ℝ (Fin d) | 0 ≤ inner ℝ y e}), K t x y = 1)) ∧
        (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → ∀ y : EuclideanSpace ℝ (Fin d), K1 t x y (b - e) = 0) := by sorry

end EthierKurtz
