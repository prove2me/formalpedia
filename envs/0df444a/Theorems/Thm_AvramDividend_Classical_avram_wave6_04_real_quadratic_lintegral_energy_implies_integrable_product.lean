-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_real_quadratic_lintegral_energy_implies_integrable_product
-- name    : AvramDividend.Classical.avram_wave6_04_real_quadratic_lintegral_energy_implies_integrable_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:23:20.041246+00:00
-- url     : https://prove2.me/theorems/6c687fd0-09c0-4440-bd60-cdc5184cac18
-- title:
--   Finite real quadratic ENNReal lintegral yields integrable squared product
-- statement:
--   A measurable real-valued function with finite ENNReal.ofReal square integral has integrable pointwise quadratic product. This converts accepted true-source predictable Taylor L2 energy to a real-valued Integrable hypothesis for source-fibre disintegration without adding probabilistic assumptions.
-- source:
--   Proof mechanism reused from independently accepted original-source Gaussian L2 energy; Mathlib HasFiniteIntegral definition and real square eNorm.

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_real_quadratic_lintegral_energy_implies_integrable_product
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f)
    (hfin : (∫⁻ a, ENNReal.ofReal ((f a) ^ 2) ∂μ) < ⊤) :
    Integrable (fun a => f a * f a) μ := by sorry
