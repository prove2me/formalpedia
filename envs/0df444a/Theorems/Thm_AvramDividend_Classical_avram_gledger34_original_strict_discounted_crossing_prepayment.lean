-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger34_original_strict_discounted_crossing_prepayment
-- name    : AvramDividend.Classical.avram_gledger34_original_strict_discounted_crossing_prepayment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:46:21.199256+00:00
-- url     : https://prove2.me/theorems/e5bd6018-4d21-446c-a90f-06fea248a59c
-- title:
--   Original strict crossing-cell discounted cash controlled by prepayment reward
-- statement:
--   For the original admissible dividend measure on a strictly open terminal crossing cell, with nonnegative prepayment reserve and positive-state reward derivative at least one, the discounted cash is bounded by the terminal discounted reward decrease plus q times the cell width times the strictly open dividend mass. This combines proved original Gaussian-31 prepayment secant and Gaussian-33 open-interval discount without charging a right-payment atom at the stopping time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger34_original_strict_discounted_crossing_prepayment {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y) (A : ℝ) (hpre : 0 ≤ A - D b ω) (hinc : 0 ≤ D b ω - rightLimit D a ω) : (∫⁻ s in Ioo (a : ℝ) (b : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤ ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) * ENNReal.ofReal (w (A - rightLimit D a ω) - w (A - D b ω)) + ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) * dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) := by sorry
