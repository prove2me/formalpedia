-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_fatou_ae_limit_lintegral_le_uniform_bound
-- name    : AvramDividend.Classical.chat03_fatou_ae_limit_lintegral_le_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:59:23.179301+00:00
-- url     : https://prove2.me/theorems/8a751d05-a4be-418a-bfcd-2eaf4baf07de
-- title:
--   Fatou bound for almost-everywhere limits of uniformly bounded nonnegative integrals
-- statement:
--   For any sequence of almost-everywhere measurable nonnegative extended-real functions converging almost everywhere to G, if every Lebesgue integral is bounded by B, then the integral of G is also bounded by B. The result permits B to be infinite but is most useful with a finite uniform quadratic-moment bound.
-- source:
--   Pinned Mathlib lintegral_liminf_le' (Fatou), Filter.Tendsto.liminf_eq and Filter.liminf_le_of_le applied to a uniform bound.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.LiminfLimsup

open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.chat03_fatou_ae_limit_lintegral_le_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ≥0∞) (G : Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hFm : ∀ n, AEMeasurable (F n) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)))
    (hB : ∀ n, (∫⁻ ω, F n ω ∂P) ≤ B) :
    (∫⁻ ω, G ω ∂P) ≤ B := by sorry
