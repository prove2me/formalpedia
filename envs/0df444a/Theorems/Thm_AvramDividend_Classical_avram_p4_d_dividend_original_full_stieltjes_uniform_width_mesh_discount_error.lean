-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:24:07.902433+00:00
-- url     : https://prove2.me/theorems/ad16e2af-ef20-467a-b491-470c91ae87e3
-- title:
--   Exact original Stieltjes mesh cash error bounded by q times width times full mass
-- statement:
--   For any finite mesh of original dividend Stieltjes payment intervals of maximum width h and any nonnegative discount rate q, the exact payment-time discounted cell cash differs upwards from its right-endpoint-discounted counterpart by at most ENNReal.ofReal(qh) times the full sum of original cell Stieltjes masses. The bound covers singular-continuous payments and closed-right endpoint atoms. A later localization step must provide a finite total mass and a vanishing maximum width to pass to the continuous mesh limit.
-- source:
--   Proved finite-mesh original Stieltjes discount error and exact ENNReal width oscillation; Avram-Palmowski-Pistorius Proposition 4(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_finite_mesh_discount_error
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_exact_discount_nnreal_width_oscillation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 ≤ h)
    (s : Finset ι) (a b : ι → ℝ≥0)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hmesh : ∀ i ∈ s, (b i : ℝ) - (a i : ℝ) ≤ h) :
    (∑ i ∈ s, ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
      dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) ≤
    (∑ i ∈ s, ∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ∧
    (∑ i ∈ s, ∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ≤
      (∑ i ∈ s, ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
        dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) +
      ENNReal.ofReal (q * h) *
        (∑ i ∈ s, dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by sorry
