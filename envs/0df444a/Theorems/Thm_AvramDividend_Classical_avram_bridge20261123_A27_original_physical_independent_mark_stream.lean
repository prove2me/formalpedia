-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A27_original_physical_independent_mark_stream
-- name    : AvramDividend.Classical.avram_bridge20261123_A27_original_physical_independent_mark_stream
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T14:03:30.989125+00:00
-- url     : https://prove2.me/theorems/6bb69384-f983-434f-a987-2d73c76a6354
-- title:
--   Original same-space physical independent negative-jump stream and moment-law witness
-- statement:
--   Construct measurable negative-jump marks on the original probability space, show fixed marked sums independent of the true Poisson count, represent original physical jumps as the first K marks, establish fixed exponential moments and identify the original Levy intensity. This remains Open and retains the original physical source problem.
-- source:
--   Canonical original A27 physical negative-jump count theorem 5afe9488-e30a-4c1f-b71f-0b7c4abb9548

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A27_original_physical_independent_mark_stream
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
    ∃ (Y : ℕ → Ω → ℝ) (m : ℝ),
      (∀ i, Measurable (Y i)) ∧
      (∀ k, IndepFun K
        (fun ω => ∑ i ∈ Finset.range k, Y i ω) P) ∧
      (∀ᵐ ω ∂P, J ω = ∑ i ∈ Finset.range (K ω), Y i ω) ∧
      (∀ k, (∫ ω, Real.exp
        (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) = m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by sorry
