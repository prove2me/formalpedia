-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_deterministic_horizon_killed_terminal_integrable
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_deterministic_horizon_killed_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:25:21.029118+00:00
-- url     : https://prove2.me/theorems/00620243-492d-4b57-938d-b63392e6b607
-- title:
--   Original positive-cap BV strictly surviving postrightpayment HJB terminal is integrable at every deterministic horizon
-- statement:
--   For the original Standing bounded-variation Levy process and any admissible capped strategy, the discounted positive-part post-rightpayment candidate terminal killed exactly on strict non-survival is integrable at every deterministic finite time.
-- source:
--   Faithful first conjunct of Avram W8-04 original strong BV stochastic verification. Uses already Proved source uniform all-clocks a.e. bound 9b971456 and exact strictly killed postrightpayment joint terminal measurability ead5faa1 to show L1 by pinned Integrable.of_bound. No generator supermartingale inequality and no strengthened ruin convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_deterministic_horizon_killed_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) :
    Integrable (fun ω =>
      if (H : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (H : ℝ))) *
          w (x + X.X H ω - rightLimit D H ω))
      else 0) P := by sorry
