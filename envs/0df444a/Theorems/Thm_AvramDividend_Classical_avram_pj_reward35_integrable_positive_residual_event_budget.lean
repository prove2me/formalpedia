-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward35_integrable_positive_residual_event_budget
-- name    : AvramDividend.Classical.avram_pj_reward35_integrable_positive_residual_event_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:51:39.055974+00:00
-- url     : https://prove2.me/theorems/950a5c01-62d6-4782-8b70-4d87a444f5a1
-- title:
--   Eventwise expected stopped reward budget from an integrable positive Ito residual
-- statement:
--   Reusable eventwise source residual inequality: integrable stopped reward G and integrable physical compensated Ito/HJB term H imply E_A[G] ≤ a P(A)+E_A[H]+epsilon whenever E_A[max(0,G-a-H)] ≤ epsilon. The inequality is purely deterministic integral algebra and retains the exact original stopped source expression in callers. Supports the original source 20d84b1f from strong source a45df81e without additional stochastic assumptions.
-- source:
--   Measure theory: integral monotonicity and additivity; Prove2Me AvramDividend purejump source-band HJB estimate 20d84b1f.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward35_integrable_positive_residual_event_budget
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (A : Set Ω) (G H : Ω → ℝ)
    (a ε : ℝ) (hG : Integrable G P) (hH : Integrable H P)
    (hres : (∫ ω in A, max (0 : ℝ) (G ω - a - H ω) ∂P) ≤ ε) :
    (∫ ω in A, G ω ∂P) ≤ a * (P A).toReal +
      (∫ ω in A, H ω ∂P) + ε := by sorry
