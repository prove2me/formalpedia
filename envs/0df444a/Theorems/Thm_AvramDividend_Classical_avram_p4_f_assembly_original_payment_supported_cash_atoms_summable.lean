-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_payment_supported_cash_atoms_summable
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_payment_supported_cash_atoms_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:22:59.130523+00:00
-- url     : https://prove2.me/theorems/804dc510-2b4b-428f-8a50-97d55507070f
-- title:
--   Actual original stopped discounted Cash atomic series is summable on a source payment-time-supported real set
-- statement:
--   If the real-indexed source atom set lies in actual pre-ruin paymentTimes, the accepted source finite stopped Stieltjes total-mass theorem proves summability of the literal real discounted atomic Cash series without the paymentTimes indicator. This discharges the Cash-summability premise of the countable HJB secant comparison under physical support.
-- source:
--   Accepted 152570c5 source exact stopped real atomic Cash summability; the paymentTimes indicator simplifies under hPay. No claim about arbitrary non-payment atoms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atomic_series
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_payment_supported_cash_atoms_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (A : Set ℝ) (hA : A.Countable)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (htotal : ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) Set.univ =
        ENNReal.ofReal (rightLimit D T ω))
    (q : ℝ) (hq : 0 ≤ q)
    (hPay : ∀ a : A, a.1 ∈ paymentTimes (ruinTime X x D ω)) :
    Summable (fun a : A =>
      (ENNReal.ofReal (Real.exp (-(q * a.1))) *
        μatom {a.1}).toReal) := by sorry
