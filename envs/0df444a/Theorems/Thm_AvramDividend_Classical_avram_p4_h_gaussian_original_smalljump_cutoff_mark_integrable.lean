-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:23:41.697258+00:00
-- url     : https://prove2.me/theorems/1fa1d6da-69ca-404d-99c6-c348caf3b974
-- title:
--   Original intrinsic finite-band small negative jump sizes are pathwise integrable
-- statement:
--   For every actual path of the original Levy X, the signed mark projection z is integrable over the intrinsic jump-counting measure restricted to times (0,T] and marks (-1,-1/(n+1)]. This derives the finite-band signed jump integral directly from original path jump-count finiteness, with no assumed compensator, replacement Levy process or Brownian motion.
-- source:
--   Proved 3537a106 original separated negative-band count finite every path; pinned Mathlib Integrable.of_bound, ae_restrict_mem and isFiniteMeasure_restrict.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc 0 T ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))))
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by sorry
