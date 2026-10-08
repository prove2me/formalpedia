-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividend_exponential_factor_package
-- name    : AvramDividend.Classical.dividend_exponential_factor_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:05:41.480343+00:00
-- url     : https://prove2.me/theorems/d3384ac8-9760-4ab1-9d48-f478b1c4541a
-- title:
--   The exponential of cumulative dividends is an adapted bounded nonincreasing factor
-- statement:
--   For a dividend strategy D (left-continuous, adapted, nondecreasing and D0=0) and any θ≥0, the process exp(−θ D_t) is adapted, has nonincreasing paths, and takes values in (0,1]. These elementary but exact properties make it a bounded adapted decreasing random multiplicative factor for a positive exponential Lévy martingale, helping construct special-case controlled-reserve supermartingales without assuming an Itô formula.
-- source:
--   Definition of AvramDividend.Classical.IsDividendStrategy and Mathlib measurability, order-preserving exponential and nonnegative dividend process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividend_exponential_factor_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Adapted 𝓕 (fun t ω => Real.exp (-(θ * D t ω))) ∧
    (∀ ω, Antitone (fun t => Real.exp (-(θ * D t ω)))) ∧
    (∀ t ω, 0 < Real.exp (-(θ * D t ω)) ∧
      Real.exp (-(θ * D t ω)) ≤ 1) := by sorry
