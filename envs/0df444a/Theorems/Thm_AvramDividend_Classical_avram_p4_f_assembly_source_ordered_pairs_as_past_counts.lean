-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_source_ordered_pairs_as_past_counts
-- name    : AvramDividend.Classical.avram_p4_f_assembly_source_ordered_pairs_as_past_counts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:54:11.475245+00:00
-- url     : https://prove2.me/theorems/1aea4cfb-0af1-4c17-a97e-955cbc65ec6b
-- title:
--   Original marked Levy ordered pair count equals sum of past marked jump counts
-- statement:
--   For the very same original spectrally negative Levy process and each sample path, the finite negative-band chronological pair count is exactly the sum, over genuine marked jump times t, of the number of genuinely marked source times strictly before t. This is the deterministic counting identity used in predictable compensator reductions of factorial second moments; no independent process or probabilistic assumption.
-- source:
--   Same original finite negative-band marked time set from Proved e5e6f70b and pinned Mathlib finite-set cardinal-sum/product formulas.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_source_ordered_pairs_as_past_counts
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card =
      ∑ t ∈ F, (F.filter (fun u => u < t)).card := by sorry
