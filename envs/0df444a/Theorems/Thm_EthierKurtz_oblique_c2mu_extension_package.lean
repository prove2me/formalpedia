-- Prove2me | Theorems.Thm_EthierKurtz_oblique_c2mu_extension_package
-- name    : EthierKurtz.oblique_c2mu_extension_package
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-28T21:59:50.457315+00:00
-- url     : https://prove2.me/theorems/e247dc64-e73e-4280-a075-5f48abfcb367
-- title:
--   $C^{2,\mu}$ extension and smoothing package from the heat kernel
-- statement:
--   For $0<\mu<1$ and every $d$: the heat-kernel smoothing $$\psi_t(x)=\int\psi(x-z)G_{2t}(z)\,dz$$ of a $C^{1,\mu}$ (resp. $C^{2,\mu}$) function satisfies the derivative, Hoelder and time-difference estimates listed in the statement.
--
--   Role: builds the $C^{2,\mu}$ extensions used to flatten the boundary.
-- source:
--   A. Friedman, Partial Differential Equations of Parabolic Type, Prentice-Hall, 1964, Chapter 1, Sections 2-4 (Gaussian kernel, heat potentials and their derivative estimates) and Chapter 5, Section 2 (oblique derivative problem in a half-space); D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7 and Lemma 6.38 (extension of $C^{k,\mu}$ functions); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem oblique_c2mu_extension_package :
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
        ∀ (μ : ℝ), 0 < μ → μ < 1 →
      ∀ (M0 M1 H : ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ψ1 : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (e : EuclideanSpace ℝ (Fin d)),
          (∀ y, HasFDerivAt ψ (ψ1 y) y) → Continuous ψ1 → (∀ y, |ψ y| ≤ M0) → (∀ y, ‖ψ1 y‖ ≤ M1) →
          (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) → 0 ≤ H → ‖e‖ = 1 →
          ∃ (E : EuclideanSpace ℝ (Fin d) → ℝ) (DE : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (D2E : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)),
            (∀ x, HasStrictFDerivAt E (DE x) x) ∧ Continuous DE ∧
            (∀ x, inner ℝ x e = 0 → E x = 0 ∧ DE x = ψ x • innerSL ℝ e) ∧
            (∀ x, 0 < inner ℝ x e → HasFDerivAt DE (D2E x) x) ∧
            ∃ C, 0 ≤ C ∧ ∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
              ‖D2E x' - D2E x‖ ≤ C * ‖x' - x‖ ^ μ := by sorry

end EthierKurtz
