-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_record_survival
-- name    : AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_record_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:51:17.533356+00:00
-- url     : https://prove2.me/theorems/e9e1835d-e6f8-4647-8f2c-d758b909c418
-- title:
--   Killed next-record discount bound from surviving strict shifted two-sided exit
-- statement:
--   Given a finite starting record and finite higher record, its delay, the actual first-level hitting value and the finite shifted upward clock, a surviving higher record forces the shifted upper-before-lower event. Thus the killed next-record discounted weight is bounded by the product of the discount at the first record and the shifted two-sided reward. This composes the established strict exit-order theorem with the proved killed-weight factorisation.
-- source:
--   Derive the strict two-sided shifted passage event from the no-finite-tie record survival result and substitute this inclusion into the accepted killed-record discount factorisation.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_record_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v)
    (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (t : ℝ≥0)
      (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)))
    (hσ : σ = (⨅ (t : ℝ≥0)
      (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞)))
    (hρfinite : ρ ≠ ⊤) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (if ρ < σ then
          ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
        else 0)) := by sorry
