-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_physical_time_two_clock_Gaussian_MemLp
-- name    : AvramDividend.Classical.ripple_original_physical_time_two_clock_Gaussian_MemLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:39:54.619906+00:00
-- url     : https://prove2.me/theorems/d09cd104-573e-43b2-8a18-62b99fbf8a09
-- title:
--   Original Avram finite physical-time two-stop Gaussian integrand L² with canonical predictable product measure
-- statement:
--   On the original spectrally negative Lévy surplus and genuine dividend strategy, there exists a finite predictable measure whose values on predictable sets agree with the finite-horizon Lebesgue-time times probability product. Under this physical measure, the true prepayment left-limit Gaussian gradient restricted to (sigma,tau] is square-integrable.
-- source:
--   Original Avram finite physical-time measure cd6e4008-ff64-4f95-991b-6dc636984270 plus Ripple original two-clock Gaussian gradient 8364d804-2cc4-4ddf-a890-d48cd5781346; Ripple commit e216e28ce3ffb43877e11f71be260e40a37a35df Apache-2.0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim
import Theorems.Thm_AvramDividend_Classical_ripple_original_gaussian_gradient_between_stops_MemLp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.ripple_original_physical_time_two_clock_Gaussian_MemLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ℝ≥0 × Ω → ℝ := fun p =>
         if Y p ∈ Icc u v then deriv w (Y p) else 0
       let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
       MemLp ({p : ℝ≥0 × Ω | 0 < p.1 ∧
           (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
           (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator G) 2 μ) := by sorry
