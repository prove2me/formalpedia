-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_iid_negative_mark_stream_source_20261117
-- name    : AvramDividend.Classical.avram_a27_original_iid_negative_mark_stream_source_20261117
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T16:06:37.46247+00:00
-- url     : https://prove2.me/theorems/952497f7-0eef-4b61-9e35-b69022d30759
-- title:
--   Original finite-activity negative marked jumps admit an IID source sequence independent of the physical count
-- statement:
--   Construct from the unchanged original spectral-negative Levy sample space a measurable full negative-mark sequence independent of the original Poisson count, with mutually independent identically distributed marks, a physical sum realisation and the exact negative-Levy mark moments and exponent.
-- source:
--   Finite-activity original marked Poisson random measure, chronological actual negative-jump enumeration and independent increments; stronger IID source certificate for A104 without source-space extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_iid_negative_mark_stream_source_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
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
    ∃ (Y : ℕ → Ω → ℝ) (m : ℝ),
      (∀ n, Measurable (Y n)) ∧
      IndepFun K (fun ω n => Y n ω) P ∧
      iIndepFun Y P ∧
      (∀ n : ℕ, IdentDistrib (Y n) (Y 0) P P) ∧
      (∀ᵐ ω ∂P, J ω = ∑ j ∈ Finset.range (K ω), Y j ω) ∧
      (∀ k : ℕ,
        (∫ ω, Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) =
          m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by sorry
