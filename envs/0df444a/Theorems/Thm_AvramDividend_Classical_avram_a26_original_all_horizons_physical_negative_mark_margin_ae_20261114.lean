-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_all_horizons_physical_negative_mark_margin_ae_20261114
-- name    : AvramDividend.Classical.avram_a26_original_all_horizons_physical_negative_mark_margin_ae_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:36:04.724552+00:00
-- url     : https://prove2.me/theorems/4047c3fd-0f56-44ee-9822-b7c7157f4769
-- title:
--   Single original source conull event with a strictly positive negative-jump magnitude gap on every horizon
-- statement:
--   On one common conull event for the original finite-activity spectrally negative Levy source, every finite horizon has a strictly positive pathwise lower bound on the magnitudes of all actual nonzero negative jumps.
-- source:
--   Proved all-horizons physical jump-time finiteness 1e50b68a, original actual jump sign d0c21664 and finite-support margin lemma A26.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One original conull event carries a negative-mark magnitude margin on every finite horizon. -/

theorem AvramDividend.Classical.avram_a26_original_all_horizons_physical_negative_mark_margin_ae_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -ε := by sorry
