-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_C1_source_weighted_partition_limit_source_drift_envelope
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_C1_source_weighted_partition_limit_source_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:45:18.706715+00:00
-- url     : https://prove2.me/theorems/e6b8413c-0b14-4004-a05a-514f5771eeda
-- title:
--   Any convergent C1 BV source weighted partition sums inherit a uniform original-source drift-only envelope
-- statement:
--   On one almost-sure samplewise event of the actual bounded-variation spectrally negative Levy source, take any sequence of ordered finite partitions with the same samplewise endpoints, coefficients bounded uniformly in absolute value by M, and a real limit of the original-source residual-weighted sums. Then the absolute value of the limit is at most M times the physical source drift-minus-original-source increment across those endpoints. The theorem does not assert convergence, stochastic integration or pure-jump equality; it supplies the path-only bound needed after convergence is independently proved in a C1 controlled chain rule.
-- source:
--   Chat04-A original-source conditional C1 limit estimate from canonical Proved source-only weighted partition envelope ae763e15-49e9-4dd0-b1b2-4168ba7d0c52 and continuity of real absolute value; no controlled stochastic integration assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Any existing real limit of uniformly bounded weighted original BV
source residual sums over refining fixed-endpoint partitions inherits
the source-only drift-path variation envelope. No Ito-Meyer identity. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_C1_source_weighted_partition_limit_source_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (s t : ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k)) (n : ℕ → ℕ)
        (hstart : ∀ k : ℕ, u k 0 = s)
        (hend : ∀ k : ℕ, u k (n k) = t)
        (a : ℕ → ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (ha : ∀ k i : ℕ, |a k i| ≤ M)
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          (Finset.range (n k)).sum (fun i =>
            a k i * (R (u k (i + 1)) - R (u k i)))) atTop (𝓝 L)),
        |L| ≤ M * (((t : ℝ) - (s : ℝ)) * X.drift -
          (X.X t ω - X.X s ω)) := by sorry
