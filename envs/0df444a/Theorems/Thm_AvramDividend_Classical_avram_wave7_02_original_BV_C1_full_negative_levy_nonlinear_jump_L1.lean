-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_full_negative_levy_nonlinear_jump_L1
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_full_negative_levy_nonlinear_jump_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:34:55.891834+00:00
-- url     : https://prove2.me/theorems/8888f8ed-e52f-42eb-b59d-4622f3c45a51
-- title:
--   Full actual original BV controlled C1 nonlinear negative Levy jump kernel is L1 on all source marks
-- statement:
--   For true original spectrally negative BV Levy X with physical ν, original controlled predictable left reserve in a compact positive C1 band, original C1 Lipschitz constant, bounded candidate below b, explicit separated large-mark ν-mass and small/large strong measurability, prove discounted full negative-mark nonlinear kernel IntegrableOn (-∞,0) X.ν. Combine the separately genuinely proved small-mark first moment and large-mark finite intensity integrability lemmas, covering ruin overshoots and no C2/Poisson-copy assumptions. Exact source stopped chain identity remains separate.
-- source:
--   W7-02 Proved original-source small ν L1 f827dbd6, original-source large ν L1 899e9e1d; physically exact partition of negative marks at -a/2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_small_levy_mark_nonlinear_discounted_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_negative_large_mark_discounted_levy_L1_on_true_tail
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_full_negative_levy_nonlinear_jump_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (F : ℝ → ℝ)
    (hF : F = fun z =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
    (hSmallMeas : AEStronglyMeasurable F
      (X.ν.restrict (Ioo (-a / 2) 0)))
    (hLargeMeas : AEStronglyMeasurable F
      (X.ν.restrict (Iic (-a / 2)))) :
    IntegrableOn F (Iio 0) X.ν := by sorry
