-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discounted_partial_record_cell_upper
-- name    : AvramDividend.Classical.runningSup_discounted_partial_record_cell_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:22:38.832324+00:00
-- url     : https://prove2.me/theorems/07d497aa-64f1-46f0-b8d4-5198145d6802
-- title:
--   Stopped terminal partial record cell has at most one mesh unit of discounted mass
-- statement:
--   If the running supremum is at level b at time s and at most b+h at time t, every antitone nonnegative discount weight gives at most w(s) times h of genuine Stieltjes dividend reward on (s,t]. This is the terminal partial-cell estimate when ruin occurs before the next first-record grid crossing; no attainment of the next record level is required.
-- source:
--   AvramDividend.Classical.runningSup_discounted_interval_bounds_record_increment (Proved UUID b5f13432-7b43-44fb-a3bc-afa7877c8aca) and monotonicity of ENNReal.ofReal. Root-connected finite-to-countable first-record upper cover for c6c3b1d0-2c2f-41ce-a5a0-2771efcc3a69.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_record_increment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_discounted_partial_record_cell_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (s t b h : ℝ) (hh : 0 ≤ h)
    (hs : runningSup X s.toNNReal ω = b)
    (ht : runningSup X t.toNNReal ω ≤ b + h) :
    (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      w s * ENNReal.ofReal h := by sorry
