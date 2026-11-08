-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian11_finitecap_initial_filtration_budget
-- name    : AvramDividend.Classical.avram_ubv_gaussian11_finitecap_initial_filtration_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-07T23:09:26.967224+00:00
-- url     : https://prove2.me/theorems/34eb0e63-df6f-4d57-899b-9e7cae3389c0
-- title:
--   Finite-cap Gaussian physical stopped reward budget on initial-filtration events
-- statement:
--   For every event A measurable at time zero in the right-continuous filtration and each k, the expected original closed-Iic stopped dividend reward F_k restricted to A is at most w(x) times P(A). This is the conditional optional-sampling budget for the same zero-jump, nondegenerate Gaussian, finite-cap HJB and admissible dividend source as the parent target.
-- source:
--   Source-faithful child of parent theorem 519b6903-ae7d-44eb-b908-c6daa2e8c6f7 in mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43 at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. The parent needs only the case A = {omega | sigma k omega != 0}; its proof will establish time-zero measurability from hσstop and specialize this stronger conditional source budget. The child imports only Mathlib and the two original Avram Definitions modules; it does not import or assume the parent theorem. Its open proof obligation is the source-exact stopped Gaussian HJB Ito/optional-sampling estimate, including dividend right-limit and closed-Iic conventions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_gaussian11_finitecap_initial_filtration_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F k ω ∂P) ≤ w x * (P A).toReal := by sorry
