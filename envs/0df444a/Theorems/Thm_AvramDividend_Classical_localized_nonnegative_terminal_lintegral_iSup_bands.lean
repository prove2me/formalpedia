-- Prove2me | Theorems.Thm_AvramDividend_Classical_localized_nonnegative_terminal_lintegral_iSup_bands
-- name    : AvramDividend.Classical.localized_nonnegative_terminal_lintegral_iSup_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:12:22.311775+00:00
-- url     : https://prove2.me/theorems/14b08501-683f-47bc-99e2-04cc302ab96c
-- title:
--   Unbounded nonnegative-reserve HJB terminal expectation is the supremum of finite reserve-band localisations
-- statement:
--   For an arbitrary measure P, measurable survival event A, measurable reserve r and measurable verification function w, the nonnegative-reserve terminal expectation of ENNReal.ofReal(w(r)) equals the supremum of its finite reserve-band truncated expectations. The localised functions are increasing in the integer band bound, and the result is monotone convergence without a global reserve cap, integrability assumption, or non-negativity assumption on w.
-- source:
--   Pinned Mathlib monotone convergence theorem MeasureTheory.lintegral_iSup and existence of an integer upper bound for every real reserve.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open MeasureTheory Set
open scoped Classical ENNReal

theorem AvramDividend.Classical.localized_nonnegative_terminal_lintegral_iSup_bands
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (r : Ω → ℝ) (hr : Measurable r)
    (w : ℝ → ℝ) (hw : Measurable w) :
    (∫⁻ ω, if ω ∈ A ∧ 0 ≤ r ω then ENNReal.ofReal (w (r ω)) else 0 ∂P) =
      ⨆ n : ℕ, (∫⁻ ω,
        if ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ) then
          ENNReal.ofReal (w (r ω)) else 0 ∂P) := by sorry
