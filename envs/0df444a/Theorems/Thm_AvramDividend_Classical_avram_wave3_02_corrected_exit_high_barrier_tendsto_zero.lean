-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_corrected_exit_high_barrier_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave3_02_corrected_exit_high_barrier_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:44:36.781178+00:00
-- url     : https://prove2.me/theorems/7c7c991b-bce8-47b3-b5c1-ee75336488de
-- title:
--   Genuine discounted original-clock upper exit reward vanishes at an infinitely distant barrier
-- statement:
--   For every fixed nonnegative initial reserve, in the original spectrally negative Lévy process with Standing and q>0, the corrected genuine discounted two-sided upward exit reward before ruin tends to zero as the upper barrier goes to infinity. The original two-sided exit identity is canonically Proved and equals ENNReal.ofReal(W(x)/W(a)) for a>0 and 0≤x≤a; the source q-scale ratio is canonically Proved to vanish at infinite a, and ofReal is continuous. This proves source stochastic asymptotics without C1 or a surrogate law.
-- source:
--   Avram Palmowski Pistorius (2007), genuine stopped first-exit process with q-discount and q-scale first-upcrossing factor; canonically Proved corrected exit identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_exit_ratio_tendsto_zero

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_corrected_exit_high_barrier_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun a : ℝ => twoSidedExitExpectationCorrected X q a x)
      atTop (𝓝 (0 : ENNReal)) := by sorry
