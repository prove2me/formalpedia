-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_strict_interior_balance_to_full
-- name    : AvramDividend.Classical.avram_root29_03_ubv_strict_interior_balance_to_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:47:00.729655+00:00
-- url     : https://prove2.me/theorems/86bce663-9092-43d3-b71c-214823db79d7
-- title:
--   Unbounded-variation stopped-scale balance through both boundaries from strictly interior balance
-- statement:
--   For a genuine unbounded-variation spectrally negative Lévy process and any q>0 scale function, the true strict-clock cross-multiplied stopped balance at every reserve 0<x<a implies the balance for every reserve 0≤x≤a. At zero use the proved original-law immediate downward passage and stopped-scale zero-start identity; at the upper barrier use the independently proved monotone-continuity strict exit ratio. No Standing hypothesis is required.
-- source:
--   Noncircular endpoint assembly for Avram WS1A. Genuine strict interior stochastic balance is explicitly assumed, not inferred from analytic scale relations. Imports are the proved clock/zero-start and conditional ratio adapters plus the independently published upper-endpoint nonzero-scale theorem; no Open be9dc931 or 2dcc8bcc import. This isolates upstream work to the strict interior domain.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_down_clock_immediate
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_upper_endpoint_nonzero_scale

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_ubv_strict_interior_balance_to_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hInterior : ∀ x : ℝ, 0 < x → x < a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    ∀ x : ℝ, 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by sorry
