-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jp20261122_original_finitecap_true_positiveclock_event_cash_source
-- name    : AvramDividend.Classical.avram_jp20261122_original_finitecap_true_positiveclock_event_cash_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T19:57:18.657572+00:00
-- url     : https://prove2.me/theorems/f4d02be4-33d3-4739-ac5c-c1bed6a0044b
-- title:
--   Source-independent original finite-cap mixed Lévy positive-clock stopped dividend event budget
-- statement:
--   The finite-cap C<top branch of the true physical ruin-clipped stopped Ito-Meyer expected reward bound on every initial filtration event restricted to positive stopping times. The function F is exactly the original discounted post-payment stopped terminal reward plus true Stieltjes dividend cash with the original paymentTimes and Iic stopping endpoint. A proof needs source-faithful bounded spatial clock Ito inequalities and genuine marked jump compensation. This is an independent source node intended to avoid the accepted cyclic alternative imports of the older finite-cap theorem 2545e563, and is the required sibling of the existing public top-cap source fff939e9 to prove active root-connected 5ca78364.
-- source:
--   Avram-Palmowski-Pistorius (2007) classical stopped dividend verification; Avram mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jp20261122_original_finitecap_true_positiveclock_event_cash_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, F ω ∂P) ≤
        w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by sorry
