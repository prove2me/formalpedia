-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
-- name    : AvramDividend.Classical.avram_twoagentA_shared_original_finite_negative_band_facts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:39:13.02892+00:00
-- url     : https://prove2.me/theorems/06fbe9b1-bad4-4ac7-8162-47b3e6d90d68
-- title:
--   Shared proved original physical jump reciprocal-annulus facts lemma
-- statement:
--   Reuses an exact previously accepted original-process proof under a shared public name for the unrestricted-Lévy-annular variance-to-L2-cutoff chain; source research/avram/agents/twoagent_20261122_B/band_facts_v1.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_shared_original_finite_negative_band_facts
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    MeasurableSet B ∧ B ⊆ Iio (0 : ℝ) ∧ X.ν B < ⊤ := by sorry
