-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_first_upExit_discount_coefficient_eq_raw_real
-- name    : AvramDividend.Classical.avram_root29_05_first_upExit_discount_coefficient_eq_raw_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:31:21.998054+00:00
-- url     : https://prove2.me/theorems/1d784900-6362-4b41-ab73-2df6ced2e13e
-- title:
--   Finite strict upcrossing discount matches the source raw two-sided-exit discount coefficient
-- statement:
--   The genuinely successful first-upcrossing discount expectation expressed using the finite NNReal clock equals the original raw upper-before-lower exit discount expressed using ENNReal.toReal, including infinity and unsuccessful paths.
-- source:
--   Apply the accepted exact raw-versus-controlled strict successful event equivalence, finite ENNReal clock under strict exit, ENNReal.coe_toNNReal, and the original exp(-q t) discount.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- On strict successful first upcrossing, the original ENNReal exit clock
has its genuine finite NNReal value, preserving the source discount. -/

theorem AvramDividend.Classical.avram_root29_05_first_upExit_discount_coefficient_eq_raw_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a q : ℝ)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (let T := twoSidedExitUpTime X (a - x)
     let R := ruinTime X x (barrierStrategy X x a)
     ∫⁻ ω, if T ω < R ω then ENNReal.ofReal
       (Real.exp (-(q * ((T ω).toNNReal : ℝ)))) else 0 ∂P) =
    (let T := twoSidedExitUpTime X (a - x)
     ∫⁻ ω, if T ω < (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q * (T ω).toReal))) else 0 ∂P) := by sorry
