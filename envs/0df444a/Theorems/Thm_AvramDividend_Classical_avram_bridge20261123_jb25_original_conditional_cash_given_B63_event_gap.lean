-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_jb25_original_conditional_cash_given_B63_event_gap
-- name    : AvramDividend.Classical.avram_bridge20261123_jb25_original_conditional_cash_given_B63_event_gap
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:14:44.260691+00:00
-- url     : https://prove2.me/theorems/66cc67d8-4a3e-421c-9bc6-a82bd5087087
-- title:
--   Original finite-cap positive-clock stopped conditional cash inequality using proved B25 two-noise event-gap obstruction
-- statement:
--   Same original positive-clock finite-activity mixed Gaussian/jump discounted dividend conditional reward upper bound for the stopped original Levy surplus. The only additional premise is the source-Proved B63 two-noise dominated event-gap impossibility for arbitrary finite-probability sample-space measure on the same Omega. The full physical sample-grid and conditional-reward estimates remain genuine Open obligations.
-- source:
--   Avram root-connected original conditional cash d8f04b83 and source-Proved abstract two-noise no-gap head 93ad5779, with four Proved B25 transitive source imports. All B25 theorem sources were authenticated as owner-proved and made public without changing Lean statements.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_jb25_original_conditional_cash_given_B63_event_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
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
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ k ω : WithTop ℝ≥0)))
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ k ω, H k ω =
      Real.exp (-(q * (κ k ω : ℝ))) *
        w (if κ k ω = 0 ∨
              (κ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω
          else riskProcess X x D (κ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hNoPositiveCashGap : (∀
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (F MG MJ BG BJ : Ω → ℝ)
    (b δ : ℝ) (hδ : 0 < δ)
    (G J E : ℕ → Ω → ℝ)
    (hFI : Integrable F P)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ᵐ ω ∂P, ∀ k, ‖G k ω‖ ≤ BG ω)
    (hJdom : ∀ᵐ ω ∂P, ∀ k, ‖J k ω‖ ≤ BJ ω)
    (hGlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hElim : ∀ᵐ ω ∂P,
      Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)))
    (hCashAll : ∀ᵐ ω ∂P, ∀ k,
      F ω ≤ b + G k ω + J k ω + E k ω)
    (hGcenter : ∀ k, (∫ ω in A, G k ω ∂P) = 0)
    (hJcenter : ∀ k, (∫ ω in A, J k ω ∂P) = 0)
    (hGap : (∫ ω in A, (fun (_ : Ω) => b) ω ∂P) + δ ≤
      (∫ ω in A, F ω ∂P)),
    False))
    :
    ∀ k, ∀ᵐ ω ∂(P.restrict {η : Ω | κ k η ≠ 0}),
      (P[H k | 𝓕.rightCont 0]) ω ≤ w x := by sorry
