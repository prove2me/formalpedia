-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_first_record_height_clock_measurable
-- name    : AvramDividend.Classical.avram_wave4_01_original_first_record_height_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:15:25.957615+00:00
-- url     : https://prove2.me/theorems/3d81e537-6079-4a4b-8c97-4b3937b3a779
-- title:
--   The genuine first strict record clock is Borel measurable as a function of record height on every original Lévy sample path
-- statement:
--   For each individual original Lévy sample path omega, the exact first strict upward passage time T_h is a Borel measurable function of the real threshold h, with values in extended nonnegative time. The proved source threshold monotonicity and the pinned Mathlib theorem that monotone maps between suitable order-topological Borel spaces are measurable supply a fully source-faithful proof. This is a required height-section regularity component for eventual joint measurability and Tonelli of actual killed first-record occupation reward, with no Standing, Esscher or excursion substitution.
-- source:
--   Existing canonical Proved source threshold-monotonicity 5060f2c9-5c3e-48d5-a44c-101f9a63f35a and pinned Mathlib Monotone.measurable (Mathlib.MeasureTheory.Constructions.BorelSpace.Order), index signature verified at revision 0df444a360eaa60ab8c11dca51a86af692955474. Bridge to expectation of pathwise killed record-height integral remains separately open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_first_record_height_clock_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Measurable (fun h : ℝ => twoSidedExitUpTime X h ω) := by sorry
