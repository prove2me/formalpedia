-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_mark_cell_mecke_recursion_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_negative_mark_cell_mecke_recursion_20261117
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T16:36:00.039929+00:00
-- url     : https://prove2.me/theorems/aec4d23b-5337-420d-8467-f38a6c273d8e
-- title:
--   Original physical negative marks satisfy the single-step Poisson count-cell Mecke recurrence
-- statement:
--   For the unchanged original filtered spectrally negative Lévy process, the exponential expectation over K=k+1 physical negative jumps equals the exponential-mark factor times r/(k+1) times the corresponding K=k expectation. The original mark rate exponent balance and normalized one-mark moment are retained. This is a genuine marked-point-process compensator source obligation, weaker than an independent infinite marked stream.
-- source:
--   The original finite-activity negative-jump marked Poisson compensator/Mecke identity and original physical count-cell process, plus deterministic Lévy exponent split. No auxiliary probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_negative_mark_cell_mecke_recursion_20261117
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
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν) ∧
      (∀ k : ℕ,
        (∫ ω in {ω : Ω | K ω = k + 1},
          Real.exp (θ * J ω) ∂P) =
        m * ((r : ℝ) / ((k + 1 : ℕ) : ℝ)) *
          (∫ ω in {ω : Ω | K ω = k},
            Real.exp (θ * J ω) ∂P)) := by sorry
