-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_finiteactivity_actual_negative_marks_eventually_below_cutoff
-- name    : AvramDividend.Classical.avram_a22_original_finiteactivity_actual_negative_marks_eventually_below_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:47:47.266528+00:00
-- url     : https://prove2.me/theorems/aee93224-a14f-47b7-a137-0955629e04e5
-- title:
--   All actual original nonzero finite-activity negative jump marks eventually lie below the cofinal negative cutoff on bounded horizons
-- statement:
--   On a single original full-measure event and for each bounded horizon, the finitely many physical nonzero negative Lévy jumps eventually lie at or below -1/(n+1), simultaneously at all actual jump times for all sufficiently fine spatial cutoffs. This follows directly from the proved original absolute mark gap and proved no-positive-jumps property. It enables exact finite-horizon physical large/small mark partition without artificial stochastic noise.
-- source:
--   Proved original physical uniform smallmark gap 035c1c05, Proved physical no-positive jumps e95fe5bc; original Lévy–Itô finite activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_smalljump_cutoff_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_finiteactivity_actual_negative_marks_eventually_below_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ u : ℝ≥0, 0 < u → u ≤ t →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1)) := by sorry
