-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_survival_terminal_integrable_of_source_bounds
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_survival_terminal_integrable_of_source_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:36:39.780211+00:00
-- url     : https://prove2.me/theorems/73908043-0c0b-4925-b58d-0e147640ef86
-- title:
--   Original BV surviving post-rightpayment discounted terminal is L1 from physical drift ceiling
-- statement:
--   On the actual spectrally negative bounded-variation Levy path, the surviving discounted post-rightpayment HJB candidate, floored at zero and killed on ruin, is integrable at every deterministic nonnegative horizon. Original dividend strategy, initial rightpayment, genuine terminal measurability and strict survival solvency enter explicitly; a Proved original BV physical drift ceiling supplies the finite compact interval even at infinite dividend cap.
-- source:
--   Avram-Palmowski-Pistorius, Proposition 4(i) and stopped inequality (5.13). Supports original BV residual 0618723a-bb0b-4fa0-94bc-4def7af7aafa; direct dependencies Proved 88e28359, 30325a04 and ef9320ae, with no stochastic budget assumed. Revision 2: uses the native NNReal deterministic horizon S to avoid ill-typed nested subtype casts in the original remote publication diagnostic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_original_BV_survival_terminal_integrable_of_source_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hInitial : ∀ ω, 0 ≤ rightLimit D 0 ω)
    (S : ℝ≥0)
    (hPostMeas : Measurable (fun ω =>
      x + X.X S ω - rightLimit D S ω))
    (hSurvivalMeas : MeasurableSet
      {ω | (S : ℝ≥0∞) < ruinTime X x D ω})
    (hSurvivalNonneg : ∀ᵐ ω ∂P,
      (S : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ x + X.X S ω - rightLimit D S ω) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0) P := by sorry
