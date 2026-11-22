-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_clock_stopped_signed_Ito_finite_activity_source
-- name    : AvramDividend.Classical.avram_jump6_B_original_positive_clock_stopped_signed_Ito_finite_activity_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T18:08:38.689257+00:00
-- url     : https://prove2.me/theorems/71cf23d9-a547-4274-8144-eebbdf57d317
-- title:
--   Avram original stopped signed Itô source for finite Lévy jump activity
-- statement:
--   On the actual original UBV ruin-clipped finite clock, construct integrable centred martingale and signed generator and dividend components all vanishing at clock zero. Establish positive-clock true discounted terminal-plus-closed-cash source budget. The zero-clock bound is already separately Proved. Additional assumption: The Lévy measure has finite total mass on the negative half-line, so the intrinsic full-jump martingale can use the finite-activity signed-Itô source and fullmark stopped-noise centring. All other source, true clock, post-payment terminal, cash, integrability, HJB and vanishing-at-zero requirements are retained verbatim.
-- source:
--   Exact case-split of Avram root-connected 81352a40-fe4f-4cb4-b96f-9705988e553a, revision 0df444a360eaa60ab8c11dca51a86af692955474. The Lévy measure has finite total mass on the negative half-line, so the intrinsic full-jump martingale can use the finite-activity signed-Itô source and fullmark stopped-noise centring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_positive_clock_stopped_signed_Ito_finite_activity_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, τ ω = 0 → M ω = 0) ∧
      (∀ᵐ ω ∂P, τ ω = 0 → G ω = 0) ∧
      (∀ᵐ ω ∂P, τ ω = 0 → H ω = 0) ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, τ ω ≠ 0 →
        Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
