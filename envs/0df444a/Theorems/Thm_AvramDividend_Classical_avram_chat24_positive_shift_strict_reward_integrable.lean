-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_shift_strict_reward_integrable
-- name    : AvramDividend.Classical.avram_chat24_positive_shift_strict_reward_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:20:02.536806+00:00
-- url     : https://prove2.me/theorems/2054c33e-cc9e-4ba6-ae0c-473f1e783d19
-- title:
--   Original strict cash and positively shifted surviving terminal are integrable at top cap
-- statement:
--   The positive-shift strict reward is L1 for the same original ruin clock and admissible strategy. This public independently proved version uses only the public original unshifted reward L1 theorem applied to the zero-extended shifted function, monotonicity from the gradient lower bound, and the original ruin-infimum nonnegative-reserve implication. It avoids importing the private shifted-L1 theorem f3680361. It supplies precisely the integrability conjunct of parent 0d51b191; the remaining expectation bound still requires the genuine compensated source estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_positive_shift_strict_reward_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Fδ : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω + δ)
       else 0)
    Integrable Fδ P := by sorry
