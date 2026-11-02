-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_real_stopped_partition_telescoping
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_real_stopped_partition_telescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:58:08.483211+00:00
-- url     : https://prove2.me/theorems/a33356a9-8d48-427c-aa85-df7513dcbd0f
-- title:
--   Original finite BV negative-jump measure mass telescopes on every stopped ordered partition
-- statement:
--   For the genuine original bounded-variation spectrally negative Levy source, on one probability-one event construct the real-valued nonnegative intrinsic negative-mark measure mass J(s,t). For every nondecreasing finite time partition, the sum of the complete original source jump masses of the successive half-open intervals equals exactly the single mass over the whole interval. This is uniform in arbitrary samplewise stopped time partitions after fixing the sample, and does not assume finite jump activity, pure-jump residual equality, an independent Poisson process or a controlled Ito-Meyer formula.
-- source:
--   Chat04-A induction on the canonically requested finite-real intrinsic measure interval functional, whose exact two-interval additivity follows from original path jump-measure additivity and BV finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Almost surely the genuine original BV negative-mark source
measure is a finite nonnegative real interval functional whose
mass telescopes exactly along every ordered finite time partition. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_real_stopped_partition_telescoping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ J : ℝ≥0 → ℝ≥0 → ℝ,
      (∀ (a b : ℝ≥0),
        J a b =
          (∫⁻ p,
            (if a < p.1 ∧ p.1 ≤ b then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal) ∧
      (∀ a b, 0 ≤ J a b) ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (∑ i ∈ Finset.range n, J (u i) (u (i + 1))) =
          J (u 0) (u n) := by sorry
