-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cell_uniform_weight_error
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_cell_uniform_weight_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:39:50.278025+00:00
-- url     : https://prove2.me/theorems/a20eda71-e1bf-443c-a90f-08221a8d4d08
-- title:
--   Uniform payment-time weight error bounds original full Stieltjes cell cash
-- statement:
--   For the exact original dividend Stieltjes measure on any payment interval (a,b], a weight lying between lo and lo+delta produces a full cell integral between lo times the entire cell mass and that quantity plus delta times the entire cell mass. This quantifies the endpoint-weighted approximation error without assuming a density or omitting singular-continuous payments or a right-endpoint atom.
-- source:
--   Proved original full Stieltjes cell-weight lintegral sandwich; Avram-Palmowski-Pistorius Proposition 4(i), (5.10)-(5.12)

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_cell_uniform_weight_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (lo δ : ℝ≥0∞) (f : ℝ → ℝ≥0∞)
    (hlo : ∀ u ∈ Ioc (a : ℝ) (b : ℝ), lo ≤ f u)
    (hhi : ∀ u ∈ Ioc (a : ℝ) (b : ℝ), f u ≤ lo + δ) :
    lo * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      (∫⁻ u in Ioc (a : ℝ) (b : ℝ), f u ∂(dividendMeasure D ω)) ∧
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ), f u ∂(dividendMeasure D ω)) ≤
      lo * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) +
        δ * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by sorry
