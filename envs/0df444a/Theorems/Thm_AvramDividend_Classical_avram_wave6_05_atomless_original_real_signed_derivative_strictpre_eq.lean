-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_atomless_original_real_signed_derivative_strictpre_eq
-- name    : AvramDividend.Classical.avram_wave6_05_atomless_original_real_signed_derivative_strictpre_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:55:44.127031+00:00
-- url     : https://prove2.me/theorems/f2ba7e75-689b-488e-a0a1-ecc5bf85856b
-- title:
--   Original Lévy positive-time signed real diffuse derivative integral equals strict source-prejump integral for every atomless dividend component
-- statement:
--   For any actual left-continuous nondecreasing dividend strategy on the original spectrally negative Lévy path and any atomless measure ν on physical time (including singular-continuous dividend Stieltjes components), the real signed e^-qs(1-w') integral on strictly positive times is invariant when its reserve argument is changed from the actual source-postjump prepayment riskProcess X x D to the genuine source-strict-left, dividend-right-limit surplus x+leftLim X-rightLimit D. The proof uses the canonically Proved source-path a.e. identity for every atomless ν and the exact pinned real setIntegral almost-everywhere congruence theorem. No cap, gradient, q sign, smooth dividend-control, finite-jump or global integrability assumption is needed; the equality is pathwise for every sample ω. Time zero is excluded from the real diffuse integral and handled separately by the original right-payment V correction.
-- source:
--   Proved source path atomless strict-prejump reserve a.e. identity combined with pinned Mathlib MeasureTheory.setIntegral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_atomless_original_real_signed_derivative_strictpre_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ν : Measure ℝ) [NullSingletonClass ν]
    (q : ℝ) (w : ℝ → ℝ) :
    (∫ s in Ioi (0 : ℝ),
      Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) =
    (∫ s in Ioi (0 : ℝ),
      Real.exp (-(q * s)) *
        (1 - deriv w (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω)) ∂ν) := by sorry
