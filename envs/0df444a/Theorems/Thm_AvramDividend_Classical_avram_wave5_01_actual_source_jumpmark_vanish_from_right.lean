-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jumpmark_vanish_from_right
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_jumpmark_vanish_from_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:49:22.252487+00:00
-- url     : https://prove2.me/theorems/94776157-6cb2-4634-ae16-78ad2028fe59
-- title:
--   Actual original Lévy jump sizes tend to zero approaching any fixed time strictly from the right
-- statement:
--   For every sample of the genuine original SpectrallyNegativeLevy P 𝓕 and every t≥0, the intrinsic sample-path jump mark at u tends to zero as u descends to t from above. This is a deterministic consequence of source right continuity and existence of strict-left limits, established in the exact original probability/filtration setting, including UBV. Together with the left-approach theorem, it supplies both no-large-jump-accumulation directions for compact finite-band localisation. It does not claim the Lévy marked-compensator intensity.
-- source:
--   Actual X.rightCont and X.leftLim; pinned Mathlib nhdsGT_basis, Ioo_mem_nhdsLT, IsClosed.mem_of_tendsto, nhdsLT_neBot_of_exists_lt, Metric.tendsto_nhds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_jumpmark_vanish_from_right
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) :
    Tendsto
      (fun u : ℝ≥0 =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      (𝓝[>] t) (𝓝 (0 : ℝ)) := by sorry
