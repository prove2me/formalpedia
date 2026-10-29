-- Prove2me | Theorems.Thm_EthierKurtz_oblique_kernel_schauder_resolvent
-- name    : EthierKurtz.oblique_kernel_schauder_resolvent
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:40:58.09565+00:00
-- url     : https://prove2.me/theorems/fbaa5e3a-d9dc-4e8a-b743-575685ce85cc
-- title:
--   Schauder resolvent estimates from abstract Gaussian kernel hypotheses
-- statement:
--   Let $K$ be a kernel on $S\subset\mathbb{R}^d$ with Gaussian bounds on its first three $x$-derivatives, the heat equation and unit mass (the hypotheses of the statement), and $0<\mu<1$. For $h$ bounded and $\mu$-Hoelder on $S$ the resolvent $$u(x)=\int_0^\infty e^{-\lambda t}\int_S h(y)K(t,x,y)\,dy\,dt$$ is $C^2$ and solves $\lambda u-\tfrac12\Delta u=h$ on $S$ with the explicit Schauder bounds of the statement.
--
--   Role: the analytic core of the half-space model.
-- source:
--   A. Friedman, Partial Differential Equations of Parabolic Type, Prentice-Hall, 1964, Chapter 1, Sections 2-4 (Gaussian kernel, heat potentials and their derivative estimates) and Chapter 5, Section 2 (oblique derivative problem in a half-space); D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 4.3-4.4 (Hoelder estimates for potentials); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem oblique_kernel_schauder_resolvent (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d)))
    (K : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (K1 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (K2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (K3 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (A c μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hK : 0 ≤ A ∧ 0 < c ∧ MeasurableSet (S) ∧ Convex ℝ (S) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K t x y) (K1 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K1 t x y) (K2 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun x => K2 t x y) (K3 t x y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), |K t x y| ≤ A * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K1 t x y‖ ≤ A * t ^ (-(1 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ‖K2 t x y‖ ≤ A * t ^ (-(1 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t)))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ (S), ∀ y ∈ (S), ∀ v w z : EuclideanSpace ℝ (Fin d),
        |K3 t x y v w z| ≤ A * t ^ (-(3 / 2 : ℝ)) * ((Real.pi * (c * t)) ^ (-((d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / (c * t))) * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K p.1 x p.2)) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K1 p.1 x p.2)) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K2 p.1 x p.2)) ∧
      (∀ x v w z : EuclideanSpace ℝ (Fin d), MeasureTheory.StronglyMeasurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) => K3 p.1 x p.2 v w z)) ∧
      (∀ t : ℝ, 0 < t → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.IntegrableOn F (S) ∧
        ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ (S), |K t x y| ≤ F y ∧ ‖K1 t x y‖ ≤ F y ∧ ‖K2 t x y‖ ≤ F y ∧
          ∀ v w z : EuclideanSpace ℝ (Fin d), |K3 t x y v w z| ≤ F y * ‖v‖ * ‖w‖ * ‖z‖) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : EuclideanSpace ℝ (Fin d), HasDerivAt (fun t => K t x y)
        ((1 / 2 : ℝ) * ∑ i, K2 t x y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) t) ∧
      (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin d), ∫ y in (S), K t x y = 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ h : EuclideanSpace ℝ (Fin d) → ℝ,
    (∃ Hh : ℝ, ∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
    (∃ M0 : ℝ, ∀ y ∈ S, |h y| ≤ M0) →
    ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r → Metric.ball x r ⊆ S →
        HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x ∈ S, lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
          = h x) ∧
      (∀ x v : EuclideanSpace ℝ (Fin d), (∀ t : ℝ, 0 < t → ∀ y ∈ S, K1 t x y v = 0) → u1 x v = 0) ∧
      ∀ M0 Hh : ℝ, 0 ≤ M0 → 0 ≤ Hh → (∀ y ∈ S, |h y| ≤ M0) →
        (∀ y ∈ S, ∀ z ∈ S, |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
      (∀ x ∈ S, ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x| ≤ C * M0 * (1 / lam) ∧
        |u1 x v| ≤ C * M0 * (1 / lam) ^ (1 / 2 : ℝ) * ‖v‖ ∧
        |u2 x v w| ≤ C * Hh * (1 / lam) ^ (μ / 2) * ‖v‖ * ‖w‖) ∧
      (∀ x ∈ S, ∀ x' ∈ S, ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x - u x'| ≤ C * M0 * (1 / lam) ^ (1 - μ / 2) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * M0 * (1 / lam) ^ ((1 - μ) / 2) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * Hh * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖) := by sorry

end EthierKurtz
