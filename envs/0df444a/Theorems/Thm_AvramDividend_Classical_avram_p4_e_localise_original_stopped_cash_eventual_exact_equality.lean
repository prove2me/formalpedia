-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_stopped_cash_eventual_exact_equality
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_stopped_cash_eventual_exact_equality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:19:38.357376+00:00
-- url     : https://prove2.me/theorems/c537da36-a5ba-4e85-a09e-c1f897f3201a
-- title:
--   Original discounted Stieltjes payout is eventually exactly stable when the genuine stopped payment domains stabilise
-- statement:
--   On the original Lévy process X, random dividend measure and actual ruin-payment convention, suppose the source's localising-clock stopped payment-domain sets eventually equal the full ruin-payment domain at a fixed horizon on an almost-sure event. The discounted original Stieltjes integral over those sets is then eventually exactly equal, including time-zero, strictly surviving fixed horizon and excluding own positive-ruin atoms. This is a direct deterministic rewrite of the genuine measure restriction, with the domain-stabilisation premise kept explicit for discharge from the Proved original Wave-7 event theorem.
-- source:
--   Original paymentTimes/ruinTime/dividendMeasure definitions; already-Proved fb083901-99df-41ea-93db-3baadff781b5, exact original payment domain stabilisation; no replacement random measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_original_stopped_cash_eventual_exact_equality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hDomains : ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T =
      paymentTimes (ruinTime X x D ω) ∩ Iic T) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
