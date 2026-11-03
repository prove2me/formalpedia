-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:06:27.020526+00:00
-- url     : https://prove2.me/theorems/7779a885-a005-45b8-8a13-634a432c7216
-- title:
--   Original-source conditional zero-cap BV counterexample to the zero-candidate full Stieltjes finite-horizon bound
-- statement:
--   Under the existence of an original Standing bounded-variation spectrally negative Lévy process with finite total negative-jump activity and q>0, the canonical barrierStrategy X 0 0 is genuinely admissible at x=0 under cap C=0, and there is a nonnegative finite integer horizon at which the complete original expected discounted Stieltjes cash fails the proposed upper bound w(0)=0 for w identically zero. This is a formal conditional counterexample to extending zero-cap BV verification with only hxc and hw0. It does not construct such an X unconditionally, and cannot change the Prove2Me status of legacy theorem 65617e0a to Disproved. The corrected target requires hC>0 and is unaffected.
-- source:
--   Source original barrierStrategy admissibility Proved 32b4ccb8 and positive finite-horizon cash theorem 09bbe99b. The latter is owned by W7-09, submitted independently, and must be Proved before this reduction itself can be Proved; while it remains Open this corollary is a genuine dependent sketch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    IsAdmissibleLe X 0 0 (barrierStrategy X 0 0) ∧
    ∃ n : ℕ, (0 : ℝ) ≤ (n : ℝ) ∧
      ¬ ((∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
          ENNReal.ofReal ((fun _ : ℝ => (0 : ℝ)) (0 : ℝ))) := by sorry
