-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_between_attained_record_levels
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_between_attained_record_levels
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T19:53:13.658354+00:00
-- url     : https://prove2.me/theorems/bb7d9d85-49b1-4aaf-a2ea-102bc6a05a2a
-- title:
--   Exact h units of actual Stieltjes dividend mass between finite first-upcrossings of successive record levels
-- statement:
--   Fix a spectrally negative Lévy path and nonnegative record heights b and b+h, with h nonnegative. If the first strict upward-passage times of these two levels are both attained at finite nonnegative times u and v, then the original running-supremum dividend Stieltjes measure of (u,v] has exact mass h. No positive-jump paths attain the record levels continuously, so the regulator equals b at u and b+h at v. The remotely accepted running-supremum dividend Stieltjes interval identity then makes the intervening mass exactly the difference h. This is the deterministic record-level mass unit required for an h-grid discretisation of the true stopped payout, without asserting any strong Markov regeneration.
-- source:
--   Accepted firstUpcrossing_attains_peak target 473109a5-7650-47ba-b397-29e7480e709e; accepted firstUpcrossing_runningSup_sub_path_eq_zero target 9243feef-85e4-45be-9f62-5e56edb2abbf; accepted runningSup_dividendMeasure_Ioc_eq_record_increment target 7343971b-047e-4925-9fa7-7ee76f6a2b23; pinned Real.toNNReal_coe in Mathlib.Data.NNReal.Defs.

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_between_attained_record_levels
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (ω : Ω) (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b + h < X.X t ω), (t : ℝ≥0∞))) :
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (u : ℝ) (v : ℝ)) = ENNReal.ofReal h := by sorry
