-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jp23_original_ubv_prepayment_leftlim_le_runningSup
-- name    : AvramDividend.Classical.avram_jp23_original_ubv_prepayment_leftlim_le_runningSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:42:57.306336+00:00
-- url     : https://prove2.me/theorems/06193581-4a0f-48e0-afed-2472452d6f14
-- title:
--   Original UBV source prepayment reserve left limit bounded by actual finite-horizon running supremum
-- statement:
--   For the ORIGINAL spectrally negative Levy surplus, every sample path, real initial capital and genuine dividend strategy D, prove without any bounded-variation hypothesis that the exact controlled prepayment left-limit Y(t)=Function.leftLim (s |-> x+X.X(s)-rightLimit D(s)) t is at most x+runningSup X T for every 0<=t<=T. Obtain pathwise upper bound X.X s<=runningSup X T from Proved runningSup_monotone_and_path_le 848fbd48 and rightLimit D s >=0 from Proved avram_ga_a35_original_dividend_rightLimit_nonnegative 8aab7ed9; then transfer the closed upper bound from all s<=t to Function.leftLim at t using the PINNED Mathlib cluster-point lemma Function.mapClusterPt_leftLim and IsClosed.mem_of_mapClusterPt for Iic bound, including at t=0 without assuming cadlag or nondegenerate left neighbourhood. This removes the original UBV left-limit-to-runningSup gap and directly supports original topcap J physical mark integrable occupation. Do not assume BV or finite cap and do not swap the prepayment left limit for terminal controlled reserve.
-- source:
--   Direct Proved 848fbd48 source path<=runningSup, 8aab7ed9 right dividend >=0, pinned Mathlib IsClosed.mem_of_mapClusterPt and Function.mapClusterPt_leftLim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_jp23_original_ubv_prepayment_leftlim_le_runningSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    ∀ (t : ℝ≥0), t ≤ T → ∀ ω : Ω,
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤
        x + runningSup X T ω := by sorry
