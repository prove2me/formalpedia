-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_small13_original_zero_prestate_negative_marks_subsingleton
-- name    : AvramDividend.Classical.avram_bv_small13_original_zero_prestate_negative_marks_subsingleton
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:50:32.2332+00:00
-- url     : https://prove2.me/theorems/892f1f86-daef-4a2e-9b3a-860c9f3437e3
-- title:
--   Original BV controlled predictable zero-reserve negative marks are subsingleton before ruin
-- statement:
--   For every original spectrally negative Levy source X and original dividend strategy D, at most one strictly positive source time before or at the original ruin clock can simultaneously have the exact original controlled predictable left pre-reserve equal to zero and a strictly negative original source jump. This is pathwise and source exact, independent of total negative-jump activity. It transports the already Proved original zero-prejump singleton bound through the already Proved positive-time original left prestate identity. It supplies the necessary count upper bound for a predictable compensator plus divergent finite-band-rate argument to remove the lower reserve boundary under infinite activity. The compensator and zero-occupation conclusion remain separate obligations.

import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_prestate_unconditional_source_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_source14_original_zero_prejump_negative_mark_subsingleton

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_small13_original_zero_prestate_negative_marks_subsingleton {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (ω : Ω) : Set.Subsingleton {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧ Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = 0 ∧ X.X t ω < Function.leftLim (fun s : ℝ≥0 => X.X s ω) t} := by sorry
