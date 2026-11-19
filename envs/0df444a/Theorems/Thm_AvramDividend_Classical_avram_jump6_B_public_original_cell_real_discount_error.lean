-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_original_cell_real_discount_error
-- name    : AvramDividend.Classical.avram_jump6_B_public_original_cell_real_discount_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:42:21.4036+00:00
-- url     : https://prove2.me/theorems/483c9f48-2205-47f9-a134-8c2f17655340
-- title:
--   Original dividend-measure real cell discount quadrature bounds with explicit source-support equality
-- statement:
--   On a nonnegative time cell [a,b], assume the actual source-restricted paymentTimes cash real integral agrees with the unmasked original dividendMeasure cash integral. The signed difference between discounted real cash and right-endpoint exponential times rightLimit D increment is nonnegative and at most q times the cell width times that increment. Follows by public finite Stieltjes mesh discount inequality, exact dividendMeasure Ioc/rightLimit identity, and finite ENNReal-to-real conversion; contains no stochastic finite-activity or independence assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_public_original_cell_real_discount_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ≥0) (hab : a ≤ b)
    (δ : ℝ) (hδ : 0 ≤ δ) (hwidth : (b : ℝ) - (a : ℝ) ≤ δ)
    (S : Set ℝ)
    (hMask :
      (∫⁻ r in S ∩ Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal =
      (∫⁻ r in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal) :
    let cash : ℝ :=
      (∫⁻ r in S ∩ Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal
    let E : ℝ := Real.exp (-(q * (b : ℝ)))
    let inc : ℝ := rightLimit D b ω - rightLimit D a ω
    0 ≤ cash - E * inc ∧ cash - E * inc ≤ q * δ * inc := by sorry
