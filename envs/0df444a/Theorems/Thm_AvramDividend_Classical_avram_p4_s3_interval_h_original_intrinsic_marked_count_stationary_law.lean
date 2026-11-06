-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:42:58.656172+00:00
-- url     : https://prove2.me/theorems/37abf3aa-adc7-4632-b669-b1e94f933d44
-- title:
--   Whole original physical Borel-marked jump count law is stationary on every deterministic shifted interval
-- statement:
--   For the original spectrally negative Levy X and its literal intrinsic marked jump measure NX on the same Ω and probability P, the full ENNReal count distribution on (s,s+T]×B equals that on (0,T]×B for every Borel B. A globally measurable càdlàg jump-count functional, the exact physical clock translation and the already proved full original future-path stationary law establish the identity. No synthetic Poisson process or substitute probability measure is introduced.
-- source:
--   Universal source càdlàg Borel-marked jump extractor 41bfd2c8, same-X clock transport b1721778, original shifted-path càdlàg, original whole-path stationarity f7f7d00c and source adapted path measurability. Extends the already Proved void-only stationarity c64a7b2a to every count distribution, enabling shifted original factorial moments.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measure.map (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B)) P =
    Measure.map (fun ω : Ω => NX ω (Ioc 0 T ×ˢ B)) P := by sorry
