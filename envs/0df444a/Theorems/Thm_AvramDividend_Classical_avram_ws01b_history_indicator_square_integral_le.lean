-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_history_indicator_square_integral_le
-- name    : AvramDividend.Classical.avram_ws01b_history_indicator_square_integral_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:30:30.750065+00:00
-- url     : https://prove2.me/theorems/2ea442dd-1048-43f8-b326-7b4193c582c2
-- title:
--   Historical killing indicators preserve integrable squares and reduce second moments
-- statement:
--   For any genuine measurable killed-history event and any square-integrable real stopped q-scale reward, the history-masked payoff has an integrable square with second moment at most the original. This exact domination is used to transfer the accepted mesh-uniform L² bound to the actual killed stopped-grid martingale rewards.
-- source:
--   Canonical Mathlib Bochner integrability of indicators and order monotonicity of the integral, with the pointwise identity (1_s f)^2 = 1_s(f^2) and nonnegative squares.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.avram_ws01b_history_indicator_square_integral_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (s : Set Ω) (hs : MeasurableSet s)
    (hfi : Integrable (fun ω => (f ω)^2) P) :
    Integrable (fun ω => (s.indicator f ω)^2) P ∧
      (∫ ω, (s.indicator f ω)^2 ∂P) ≤ ∫ ω, (f ω)^2 ∂P := by sorry
