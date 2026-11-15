-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_zero_clock_ruinclipped_full_Iic_cash_initial_condexp_upper
-- name    : AvramDividend.Classical.avram_b24_original_zero_clock_ruinclipped_full_Iic_cash_initial_condexp_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:20:17.924172+00:00
-- url     : https://prove2.me/theorems/640d50f6-becb-49f6-a98d-504a14eef10a
-- title:
--   Original finiteactivity stopped cash initial conditional upper at almost-sure zero clock, retaining time-zero right dividend
-- statement:
--   Under the exact original Standing mixed Lévy finiteactivity HJB and capped-admissible D assumptions of b235, and a ruin-clipped stopping clock σ equal to zero P-a.s., prove the same initial-filtration conditional cash bound E[F|𝓕.rightCont 0]≤w(x). The genuine original F includes postpayment terminal w at σ and discounted Stieltjes dividendMeasure over paymentTimes∩Iic(σ), retaining the time-zero right payment. Apply Proved a2629a86 exact pathwise zero-clock bound on the a.e. zero event, then monotonicity of conditional expectation and exact constant conditional expectation under original probability P. This isolates the zero-clock branch independently of Gaussian Itô energy and the unresolved strictly-positive stopping source.
-- source:
--   Proved a2629a86 zero-clock right-atom payoff + Mathlib condExp_mono, condExp_const; original b235 dd210e0a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_zero_clock_ruinclipped_full_Iic_cash_initial_condexp_upper
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
    (hσzero : ∀ᵐ ω ∂P, σ ω = 0) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ w x := by sorry
