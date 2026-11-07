-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_finite_stopped_reserve_le_barrier
-- name    : AvramDividend.Classical.avram_p4_f7_hjb_finite_stopped_reserve_le_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:44:30.137238+00:00
-- url     : https://prove2.me/theorems/aef04997-0bf8-446e-9749-7e50e5c86e16
-- title:
--   Original finite three-way stopped Lévy path remains below its upper barrier
-- statement:
--   On any original spectrally negative Levy path with no positive jumps, clipping the first strict upper exit with the corrected lower exit and a finite n still leaves its stopped path value at most the upper level b-1. This is the global bounded reserve potential upper envelope needed to justify integrability in the HJB reward-to-terminal real-expectation comparison df0e45ff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f7_hjb_finite_stopped_reserve_le_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (b : ℝ) (n : ℕ) (hb : 1 ≤ b) (ω : Ω) :
    X.X
      (ENNReal.toNNReal
        (min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞)))) ω ≤
      b - 1 := by sorry
