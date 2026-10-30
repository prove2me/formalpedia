-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_dividend_Ico_split
-- name    : AvramDividend.Classical.avram_wave3_04_discounted_dividend_Ico_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:41:40.987413+00:00
-- url     : https://prove2.me/theorems/81b977e6-4ae6-4add-b4a9-fac1caebee9c
-- title:
--   Exact two-cell decomposition of the complete discounted dividend Stieltjes reward
-- statement:
--   For an actual source dividend strategy, any two successive nonnegative-time half-open cells partition the full discounted Stieltjes payout exactly. The result holds for all real discount parameters q, includes diffuse and singular-continuous payouts and right dividend jumps, and is insensitive to an atom at the splitting time thanks to the [a,b) and [b,c) endpoint convention.
-- source:
--   Mathlib MeasureTheory.lintegral_union, measurableSet_Ico, and disjoint consecutive Ico sets. Full source reached the intentional remote compiler sentinel on pinned Mathlib, candidate SHA-256 8244510e722fd298e3475b85de7fb1f0faf9d103af180d9aee7078a542fbe00e, job a9d87206-71ab-42aa-9446-aad4934138cf. This is the exact finite-grid splitting bridge for original dividendMeasure integration in Avram Palmowski Pistorius (2007), Proposition 4(i), avoiding the Disproved atomic-concentration reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_discounted_dividend_Ico_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (a b c : ℝ≥0)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∫⁻ s in Ico (a : ℝ) (c : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
    (∫⁻ s in Ico (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    (∫⁻ s in Ico (b : ℝ) (c : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by sorry
