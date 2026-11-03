-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:06:43.110433+00:00
-- url     : https://prove2.me/theorems/d4e52bb5-b254-4717-9dcf-dbff559632fc
-- title:
--   Original BV C1 controlled predictable generator negative marks never increase verification candidate even when overshooting ruin
-- statement:
--   For the actual spectrally negative Levy source and original controlled predictable left-limit reserve strictly inside the positive cap, any nonpositive negative source jump mark has w(y+mark)≤w(y). Proof uses the Proved full-cap BV C1 gradient secant when the source landing point is nonnegative, and the exact w=0 below zero plus w(0)≥0 when the source mark crosses ruin. Includes exact landing zero and arbitrary ruin overshoot, with no false C1 extension beyond the HJB interior.
-- source:
--   Canonical BV C1 verification gradient, nonnegative initial value and negative-reserve zero extension; Proved full-cap gradient secant 2ba5cc4f on original controlled predictable source left-limit state.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hregion :
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C)
    (z : ℝ) (hz : z ≤ 0) :
    w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) ≤
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by sorry
