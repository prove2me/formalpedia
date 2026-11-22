-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_Brownian_stopped_gaussian_source
-- name    : AvramDividend.Classical.ripple_original_zerojump_Brownian_stopped_gaussian_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:03:32.271803+00:00
-- url     : https://prove2.me/theorems/81acb9c7-a1ae-4736-9b8b-7aca67791228
-- title:
--   Original zero-jump Brownian physical stopped driver plus two-stop Gaussian L2 source
-- statement:
--   A genuine filtered Brownian driver of the original stopped zero-jump Avram process exists on the same path space, with actual stopped reserve and dividend source. The original prepayment gradient restricted to two physical stopping times is square integrable under a finite predictable measure representing the physical horizon time by probability product.
-- source:
--   Original Avram same-space stopped Brownian theorem 68bc4dba-badb-421b-9535-ae83ac29f82a with true Ripple-derived physical-time two-clock Gaussian gradient theorem d09cd104-573e-43b2-8a18-62b99fbf8a09, ultimately Ripple/Stochastic/StoppedPredictableIntegrand.lean commit e216e28ce3ffb43877e11f71be260e40a37a35df Apache-2.0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_postpayment_stopped_sameBrownian
import Theorems.Thm_AvramDividend_Classical_ripple_original_physical_time_two_clock_Gaussian_MemLp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.ripple_original_zerojump_Brownian_stopped_gaussian_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (ℱr : Filtration ℝ mΩ)
      (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
      LevyStochCalc.Brownian.IsBrownianFiltration B ℱr ∧
      IsStoppingTime ℱr
        (fun ω => ((τ ω : ℝ) : WithTop ℝ)) ∧
      (∀ (t : ℝ≥0) (ω : Ω),
        riskProcess X x D t ω =
          x + (t : ℝ) * X.c + X.σ * B.W (t : ℝ) ω - D t ω) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
         (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ℝ≥0 × Ω → ℝ := fun p =>
         if Y p ∈ Icc u v then deriv w (Y p) else 0
       let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
       MemLp ({p : ℝ≥0 × Ω | 0 < p.1 ∧
         (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
         (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator G) 2 μ) := by sorry
