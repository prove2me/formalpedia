-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_finite_significant_jump_finset
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_finite_significant_jump_finset
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:03:07.470409+00:00
-- url     : https://prove2.me/theorems/33f1225f-cfaf-4b48-b05d-ced2a38d62ea
-- title:
--   Exact finite original-path significant-jump selector
-- statement:
--   For every sample path of the original spectrally negative Lévy process and every finite horizon, the set of strictly positive jump times with absolute real jump size at least rho is represented by a genuine finite Finset, with exact membership equivalence. Use the existing original-source compact significant-jump finiteness theorem. No replacement process, finite-activity assumption, or compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_finite_significant_jump_finset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ F : Finset ℝ≥0, ∀ t : ℝ≥0,
      t ∈ F ↔ 0 < t ∧ t ≤ T ∧
        ρ ≤ |X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t| := by sorry
