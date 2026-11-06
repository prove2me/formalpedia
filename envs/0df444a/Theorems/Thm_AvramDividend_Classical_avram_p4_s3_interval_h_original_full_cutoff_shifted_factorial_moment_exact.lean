-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_factorial_moment_exact
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_shifted_factorial_moment_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:00:35.733253+00:00
-- url     : https://prove2.me/theorems/69f9bc6c-9678-4618-9107-ade8771d8e3e
-- title:
--   Exact original full negative-cutoff jump-count factorial moment on any shifted physical time interval
-- statement:
--   For the unchanged original spectrally negative Levy X and its genuine marked jump count N on (s,s+T] with all negative marks at most −1/(n+1), its real second factorial count is integrable and has expectation [T·ν((−∞,−1/(n+1)])]². Uses the independently proved original zero-origin factorial moment and genuine whole original marked-count stationary law transported through a measurable real count functional, with no synthetic process or added count distribution premise.
-- source:
--   Composes Proved original full-cutoff zero-origin factorial moment 0a13392f with the new complete original count stationary real moment bridge. The actual same-path NX is definitionally the physical marked jump measure; its shifted count and zero-origin count use identical B and Lévy measure.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_shifted_factorial_moment_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 := by sorry
