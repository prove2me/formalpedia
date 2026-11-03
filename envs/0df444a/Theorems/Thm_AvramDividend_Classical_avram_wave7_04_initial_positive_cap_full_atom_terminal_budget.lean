-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_04_initial_positive_cap_full_atom_terminal_budget
-- name    : AvramDividend.Classical.avram_wave7_04_initial_positive_cap_full_atom_terminal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:43:05.164467+00:00
-- url     : https://prove2.me/theorems/82bf9d2c-e88a-40bb-93d6-87a197c33510
-- title:
--   Original BV positive-cap time-zero full Stieltjes atom and surviving terminal pathwise budget
-- statement:
--   In the original filtered spectrally negative Levy model, under positive cap, BV, nonnegative w(0), C1 and slope at least one on the positive interior, and right-jump dominance, the time-zero full Stieltjes cash atom plus the surviving post-rightpayment terminal value is bounded pathwise by w(x). Unlike the weaker zero-clock base, post-payment value nonnegativity is derived from positive-cap admissibility and gradient hypotheses, not assumed.
-- source:
--   A nontrivial source-faithful strengthening of Proved W7-04 initial full-atom terminal lemma 50981c17-6933-436c-96ca-d1c588725de1. Uses Proved W5-03 chronological stopped terminal nonnegativity f72f93f3-cfbf-4a71-b625-a1d0576710c0 specialised to the true time-zero clock, BV C1 and original positive cap. This is the exact zero-clock terminal base for the Open stopped BV Ito supermartingale 0618723a-bb0b-4fa0-94bc-4def7af7aafa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_04_initial_positive_cap_full_atom_terminal_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (0 : ℝ≥0∞) < ruinTime X x D ω then
       max 0 (w (x - rightLimit D 0 ω))
     else 0) ≤ w x := by sorry
