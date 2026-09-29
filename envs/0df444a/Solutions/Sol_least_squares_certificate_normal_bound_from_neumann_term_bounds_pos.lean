-- Prove2me | solution 1 for least_squares_certificate_normal_bound_from_neumann_term_bounds_pos
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T23:35:51.421595+00:00
-- url     : https://prove2.me/submissions/cc5ff08f-32d3-4e59-b4e5-2e038d21a79e

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_neumann_term_bounds_imply_least_squares_certificate_normal_bound_pos
import Theorems.Thm_bernoulli_finite_index_intersection_probability_from_pointwise_bounds
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Reduction of `least_squares_certificate_normal_bound_from_neumann_term_bounds_pos`
(8feb62b1_pos) — the corrected Bernoulli normal-bound node that adds `0 < p` and a
high-probability concentration event — to:
  - the pointwise corrected node `neumann_term_bounds_imply_least_squares_certificate_normal_bound_pos`
    (22bf6cfe_pos),
  - the proved finite-index intersection bound
    `bernoulli_finite_index_intersection_probability_from_pointwise_bounds`,
  - the proved `bernoulli_event_probability_mono`.

A finite union bound over the FIVE high-probability inputs (concentration + the three
head term bounds + the tail bound) intersects them; on the intersection the pointwise
corrected node forces `spectralNorm (normalProjection S Y) < 1` for every certificate Y;
monotonicity lifts the intersection probability to the normal-bound event.

Source: Candès–Recht 2009 (arXiv:0805.4471), §4.3 (finite union bound over the
Neumann-term high-probability estimates) + §4.2 (the concentration/invertibility input
the disproved 8feb62b1 omitted).
-/

open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1:ℝ)/2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p 0 ((1:ℝ)/8)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p 1 ((1:ℝ)/8)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p 2 ((1:ℝ)/8)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTailSpectralBound Omega S p 3 ((1:ℝ)/2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega =>
          ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
            LeastSquaresDualCertificate Omega S Y →
            spectralNorm (normalProjection S Y) < 1) ≥
      1 - ((5 : ℝ) * c) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp1 hConc hb0 hb1 hb2 hbt
  classical
  set fs := Real.rpow (↑(max n₁ n₂)) (-β) with hfs
  let Event : Fin 5 → Finset (Fin n₁ × Fin n₂) → Prop := fun i Omega =>
    match i with
    | 0 => TangentSamplingConcentration Omega S p ((1:ℝ)/2)
    | 1 => NeumannCertificateTermSpectralBound Omega S p 0 ((1:ℝ)/8)
    | 2 => NeumannCertificateTermSpectralBound Omega S p 1 ((1:ℝ)/8)
    | 3 => NeumannCertificateTermSpectralBound Omega S p 2 ((1:ℝ)/8)
    | 4 => NeumannCertificateTailSpectralBound Omega S p 3 ((1:ℝ)/2)
  have hall : ∀ i, bernoulliEventProb p (Event i) ≥ 1 - c * fs := by
    intro i
    fin_cases i
    · exact hConc
    · exact hb0
    · exact hb1
    · exact hb2
    · exact hbt
  have hInter := bernoulli_finite_index_intersection_probability_from_pointwise_bounds
    (ι := Fin 5) p c fs Event (le_of_lt hp) hp1 hall
  have hcard : (Fintype.card (Fin 5) : ℝ) = 5 := by simp
  rw [hcard] at hInter
  refine le_trans hInter ?_
  apply bernoulli_event_probability_mono p
    (fun Omega => ∀ i, Event i Omega)
    (fun Omega => ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
      LeastSquaresDualCertificate Omega S Y →
      spectralNorm (normalProjection S Y) < 1)
    (le_of_lt hp) hp1
  intro Omega hOmega
  have hC := hOmega 0
  have h0 := hOmega 1
  have h1 := hOmega 2
  have h2 := hOmega 3
  have h4 := hOmega 4
  simp only [Event] at hC h0 h1 h2 h4
  exact neumann_term_bounds_imply_least_squares_certificate_normal_bound_pos
    S Omega p hp hC h0 h1 h2 h4
