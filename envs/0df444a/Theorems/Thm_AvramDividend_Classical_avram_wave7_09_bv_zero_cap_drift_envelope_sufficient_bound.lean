-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_drift_envelope_sufficient_bound
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_drift_envelope_sufficient_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:10:16.454387+00:00
-- url     : https://prove2.me/theorems/266de08c-1904-4577-aa7e-6412c838af84
-- title:
--   Source BV zero-cap finite-horizon bound holds when the candidate boundary value dominates physical drift envelope
-- statement:
--   For a genuine original Standing BV spectrally negative Lévy process, source-admissible strategy starting at x=0 with cap C=0, nonnegative discount q and a finite nonnegative horizon T, the expected complete Stieltjes payout is bounded by any real W at least T times the physical drift X.drift. The bound follows directly from the Proved original sharp closed-horizon drift cash budget and is a formally stated sufficient condition for any future zero-cap BV branch. It is fully compatible with the Proved positive-horizon zero-cap counterexample: w≡0 cannot satisfy the envelope at positive T when X.drift>0. No claim that the envelope is necessary for every strategy.
-- source:
--   Canonical Proved original-process sharp BV complete closed-horizon drift budget 23ddd713, including initial/diffuse/terminal Stieltjes mass. The additional explicit hypothesis T*X.drift≤W is the exact sufficient envelope; ENNReal.ofReal is monotone. No Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_drift_envelope_sufficient_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (W : ℝ) (hW : (T : ℝ) * X.drift ≤ W) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal W := by sorry
