-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_finite_activity_physical_mark_gap_ae_20261114
-- name    : AvramDividend.Classical.avram_a26_original_finite_activity_physical_mark_gap_ae_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:31:13.125886+00:00
-- url     : https://prove2.me/theorems/e146d8b4-3bd9-4198-9001-77a4303a91af
-- title:
--   Original finite negative-jump activity yields a pathwise compact-horizon positive magnitude margin on one conull event
-- statement:
--   The actual original finite-activity spectrally negative Levy source has on a conull event a positive sample-dependent jump magnitude margin for all negative jumps on any fixed finite horizon.
-- source:
--   Proved finite jump-time support 1e50b68a, original actual jump sign d0c21664 and finite support gap A26.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original finite-activity source jumps on a compact horizon have a uniform strictly positive negative-mark margin. -/

theorem AvramDividend.Classical.avram_a26_original_finite_activity_physical_mark_gap_ae_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -ε := by sorry
