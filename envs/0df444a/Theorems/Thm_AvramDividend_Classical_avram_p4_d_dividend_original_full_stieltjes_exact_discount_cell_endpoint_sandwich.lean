-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_endpoint_sandwich
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_endpoint_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:37:29.219578+00:00
-- url     : https://prove2.me/theorems/ee2fcfcd-a5a0-4f2c-9cc5-c2ded4cc8aae
-- title:
--   Exact source discounted Stieltjes cell cash lies between endpoint-weighted full cell masses
-- statement:
--   The exact original discounted Stieltjes integral over any closed-right payment cell lies between its endpoint discount factors times full unweighted cell mass. This source measure fact preserves singular-continuous payment mass and the horizon right atom and uses no unproved density or absolute-continuity assertion. It is the rigorous within-cell discount error control needed by the forthcoming controlled finite-variation chain mesh limit.
-- source:
--   Proved P4-D original full Stieltjes cell-weight measure sandwich; Avram-Palmowski-Pistorius Proposition 4(i), (5.10)-(5.12)

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_endpoint_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      (∫⁻ u in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ∧
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by sorry
