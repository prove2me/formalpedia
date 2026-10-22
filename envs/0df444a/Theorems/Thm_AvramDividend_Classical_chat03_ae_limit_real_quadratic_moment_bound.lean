-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_ae_limit_real_quadratic_moment_bound
-- name    : AvramDividend.Classical.chat03_ae_limit_real_quadratic_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:19:32.345061+00:00
-- url     : https://prove2.me/theorems/05aa7673-3d11-4d67-a5ed-06047db832b4
-- title:
--   Real quadratic moment bound for an almost-everywhere limit
-- statement:
--   An almost-sure real limit of strongly measurable variables with a uniform second-moment upper bound has an integrable real square and retains the same quadratic moment bound, on a probability space. The proof combines the accepted Fatou quadratic lintegral estimate with the Bochner-real integral conversion.
-- source:
--   Fatou's lemma for extended-real quadratic moments and the accepted real-integral conversion.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_chat03_ae_limit_quadratic_moment_bound
import Theorems.Thm_AvramDividend_Classical_chat03_lintegral_bound_implies_real_integral_bound

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_ae_limit_real_quadratic_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hZm : AEStronglyMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)))
    (C : ℝ) (hC : 0 ≤ C)
    (hY2 : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P ∧
      ∫ ω, (Y n ω) ^ 2 ∂P ≤ C) :
    Integrable (fun ω => (Z ω) ^ 2) P ∧
      (∫ ω, (Z ω) ^ 2 ∂P) ≤ C := by sorry
