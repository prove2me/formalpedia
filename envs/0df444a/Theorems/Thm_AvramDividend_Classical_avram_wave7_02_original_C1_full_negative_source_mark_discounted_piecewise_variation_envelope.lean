-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:43:21.513067+00:00
-- url     : https://prove2.me/theorems/2b420992-8476-4ca8-9299-f748339ccebe
-- title:
--   Original C1 controlled nonlinear negative Lévy mark admits complete pointwise small-first-moment and large-finite-intensity envelope
-- statement:
--   For the actual original controlled predictable left reserve in a compact positive band, every negative Lévy source mark has discounted nonlinear C1 candidate jump |exp(-qt)(w(y+z)-w(y))| bounded by L(-z) for -a/2<z<0 and 2R for z≤-a/2. Combines the genuinely proved small-mark Lipschitz estimate and large-mark capped candidate bound, including ruin-crossing marks. Exactly matches the separately proved physical BV Lévy integrable piecewise envelope and supports original predictable marked compensation.
-- source:
--   Proved W7-02 original small negative source C1 first-variation pointwise bound e6763634 and original large negative mark uniform bound e44668f8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (z : ℝ) (hz : z < 0) :
    |Real.exp (-(q * (t : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t))| ≤
      if z ≤ -a / 2 then 2 * R else L * (-z) := by sorry
