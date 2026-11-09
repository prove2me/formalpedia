-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_controlled_survival_masked_C2_weights
-- name    : AvramDividend.Classical.avram_ubv_gauss13_stop_original_controlled_survival_masked_C2_weights
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:59:59.048651+00:00
-- url     : https://prove2.me/theorems/ee060ece-19cf-49ea-9fc0-d8c867c5a8d2
-- title:
--   Actual original dividend-controlled discounted C2 Gaussian weights remain predictable on the genuine stopped physical left grid
-- statement:
--   Direct source-specialised proof import for original finite-cap Gaussian physical C2 witness a338c453-58c0-411c-aaca-5cec689ed807 and new strict HJB child c31f81c8-6052-4a7f-af24-72e0e1944c00, with top-cap consumer 249c532d-4ec0-498c-81f0-b380dd476344. The actual prepayment left-limit discounted gradient and capped Hessian of the original X,D,w process, including finite horizon and inclusive ruin indicator, are strongly predictable by existing source Proved theorems 658fb6a1 and 8902785a. The Proved new true sampled survival theorem 2f3d862d transfers both coefficients through the exact random final included left-grid cell in the original right-continuous filtration. No floor-clock stopping assumption, no auxiliary process. This closes the actual-coefficient measurability interface, not pathwise Ito-Stieltjes inequality or L1 mesh convergence.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_sampled_survival_predictable_coefficients
open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_stop_original_controlled_survival_masked_C2_weights
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (K : Ω → ℕ)
    (hK : IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ))) :
    let G : ℝ≥0 → Ω → ℝ :=
      fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0
    let H : ℝ≥0 → Ω → ℝ :=
      fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0
    ∀ i,
      Measurable[𝓕.rightCont (e i)]
        (fun ω => if i < K ω then G (e i) ω else 0) ∧
      Measurable[𝓕.rightCont (e i)]
        (fun ω => if i < K ω then H (e i) ω else 0) := by
  sorry
