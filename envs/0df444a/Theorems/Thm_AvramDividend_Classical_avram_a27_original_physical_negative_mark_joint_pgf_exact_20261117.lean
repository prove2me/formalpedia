-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_mark_joint_pgf_exact_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_negative_mark_joint_pgf_exact_20261117
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:48:50.930286+00:00
-- url     : https://prove2.me/theorems/ee60897e-c8ce-485e-9d1e-3869c5b2d97b
-- title:
--   Original physical marked negative-jump joint probability generating function has the exact Lévy exponential transform
-- statement:
--   For the unchanged original probability space and physical finite-activity spectrally negative Lévy jump process, the joint count-mark transform E[z^K exp(theta J)] equals exp(((r+t integral(exp(theta y)-1)nu)*z)-r), for z from zero to one. Establish from the original marked jump measure's predictable compensation or finite marked partitions, without independent manufactured marks.
-- source:
--   The original physical jump counting measure is a time-homogeneous Poisson random measure with intensity dt nu(dy); derive its Laplace functional using original adapted finite jump product and predictable compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_negative_mark_joint_pgf_exact_20261117
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
    ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) =
        Real.exp (((r : ℝ) + (t : ℝ) * (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) * z - (r : ℝ)) := by sorry
