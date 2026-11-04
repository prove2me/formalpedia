-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_finite_mesh_discount_error
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_finite_mesh_discount_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:05:43.09395+00:00
-- url     : https://prove2.me/theorems/77fd9326-eaa5-4ddd-9531-4329b44f982c
-- title:
--   Finite mesh exact discounted original Stieltjes cash has explicit oscillation error budget
-- statement:
--   For a finite collection of original dividend payment cells and nonnegative discount q, suppose the discount oscillation across each cell is bounded by a nonnegative budget delta. Then the exact discounted full Stieltjes lintegral summed over all cells lies between the endpoint-discounted cell masses and their sum plus the summed delta-times-cell-mass errors. No density or atomlessness assumptions are made. This prepares mesh-limit control of the original absolutely continuous, singular continuous, and endpoint atom payments.
-- source:
--   Proved original Stieltjes uniform cell weight error; controlled finite variation approximation in Avram-Palmowski-Pistorius Proposition 4(i), (5.10)-(5.12)

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cell_uniform_weight_error

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_finite_mesh_discount_error
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (s : Finset ι) (a b : ι → ℝ≥0) (δ : ι → ℝ≥0∞)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hδ : ∀ i ∈ s,
      ENNReal.ofReal (Real.exp (-(q * (a i : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) + δ i) :
    (∑ i ∈ s, ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
      dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) ≤
    (∑ i ∈ s, ∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ∧
    (∑ i ∈ s, ∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ≤
      (∑ i ∈ s, ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
        dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) +
      (∑ i ∈ s, δ i * dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by sorry
