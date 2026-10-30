-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_discount_at_finite_stopped_min
-- name    : AvramDividend.Classical.avram_root29_03_exit_discount_at_finite_stopped_min
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:19:20.617647+00:00
-- url     : https://prove2.me/theorems/86bf8a71-56f7-441b-a30b-40dbf493908d
-- title:
--   Actual upper-exit discount computed at the finite minimum stopped clock
-- statement:
--   For a positive upper exit barrier, the exact original-Lévy ENNReal discounted two-sided upper-before-lower reward can be evaluated at min of the actual upward and downward strict passage clocks, conditioned by weak upper-first order and upper-clock finiteness. Original law P and its integrand are preserved. All real q and reserve x, no Standing.
-- source:
--   Noncircular stopped-discount normalisation using already canonically Proved cf1d1161 and pointwise min_eq_left on the strict-event support. Does not rely on any unproved killed process harmonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_strict_up_event_iff_finite_weak_order

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_exit_discount_at_finite_stopped_min
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a x : ℝ) (ha : 0 < a) :
    twoSidedExitExpectation X q a x =
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω ≤ twoSidedExitDownTime X (-x) ω ∧
          twoSidedExitUpTime X (a - x) ω < ⊤ then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (min (twoSidedExitUpTime X (a - x) ω)
               (twoSidedExitDownTime X (-x) ω)))))
      else 0 ∂P) := by sorry
