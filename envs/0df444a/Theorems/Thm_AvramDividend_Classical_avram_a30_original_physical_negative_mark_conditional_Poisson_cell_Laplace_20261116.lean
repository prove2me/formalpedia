-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a30_original_physical_negative_mark_conditional_Poisson_cell_Laplace_20261116
-- name    : AvramDividend.Classical.avram_a30_original_physical_negative_mark_conditional_Poisson_cell_Laplace_20261116
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T18:04:45.050093+00:00
-- url     : https://prove2.me/theorems/e22c0993-8a7c-43b3-825d-39ec6c32ea64
-- title:
--   The original finite-activity negative-jump Laplace transform admits exact Poisson count-cell conditional moments
-- statement:
--   Let K be the exact original-space negative physical jump count on (0,t], with its already proved Poisson(r) law. Conditional on K=k, the integral of exp(theta times the actual full negative-jump sum J) over this original source event equals the Poisson mass of k times the k-th power of the single negative-mark Laplace moment m. The rate balance r(m-1) equals the Levy negative-mark exponent and m^k is Poisson-integrable. This source-conditional Laplace law is weaker than constructing an infinite iid marked sequence independent of K; it avoids any auxiliary randomisation and is the remaining genuinely probabilistic marked-Poisson input needed with a generic count-cell integration lemma.
-- source:
--   Kyprianou (2006) Chapter 2 Levy–Ito decomposition and Poisson random measures; original Prove2Me count law avram_a20_original_negative_borel_count_poisson_law; generic Poisson conditional count-cell Laplace lemma a30.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a30_original_physical_negative_mark_conditional_Poisson_cell_Laplace_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hK : Measurable K) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (hRate : (r : ℝ) =
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∃ m : ℝ,
      Integrable (fun k : ℕ => m ^ k) (poissonMeasure r) ∧
      (∀ k : ℕ,
        (∫ ω in {ω : Ω | K ω = k},
          Real.exp (θ * J ω) ∂P) =
          (poissonMeasure r).real {k} * m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν) := by sorry
