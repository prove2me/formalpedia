-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_HJB_conditional_cash_failure_ae
-- name    : AvramDividend.Classical.avram_bvb_original_uniform_HJB_conditional_cash_failure_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T11:15:56.292474+00:00
-- url     : https://prove2.me/theorems/26213c61-2112-4335-ab6f-544767c7f457
-- title:
--   Source-exact Standing BV HJB and admissibility coexist with failure of the a.e. nojump-conditioned drift-only cash limit
-- statement:
--   For a single genuine Standing BV unit-drift uniform compound-Poisson source, the half-affine candidate satisfies its original HJB and the zero-barrier strategy is admissible. Nevertheless the nojump-conditioned actual original strict clipped cash-plus-terminal physical drift-only positive-part limit fails almost everywhere on a positive-probability set. The conditional nature matches the pathological zero-contact survivor branch of the BV B theorem.
-- source:
--   Use proved original full HJB witness with its positive-probability unit-linear nojump event, and proved original unit-linear pathwise stopped cash positive-part nonconvergence. A probability-zero failure-set contradiction proves non-a.e. conditional convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_original_uniform_HJB_conditional_cash_failure_ae :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧ X.drift = 1 ∧
      (let D := barrierStrategy X 0 0
       let T : ℝ := 1 / 10
       let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
       let u : ℕ → ℕ → ℝ≥0 := fun n i =>
         ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
       let F : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
         (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
             Iio (T - T / ((n : ℝ) + 2)),
           ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
           (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
             Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
            else 0)
       let L : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
         let Z : ℕ → ℝ := fun i => Function.leftLim
           (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
         ∑ i ∈ Finset.range (n + 1),
           if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
             Real.exp (-(u n i : ℝ)) *
               (X.drift * deriv w (Z i) - w (Z i)) *
               ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
       IsAdmissibleLe X 0 (1 : ℝ≥0∞) D ∧
       (∀ y : ℝ, 0 < y → ENNReal.ofReal y < (1 : ℝ≥0∞) →
         X.GeneratorIntegrable w y ∧ X.generator w y - w y ≤ 0) ∧
       ¬ (∀ᵐ ω ∂P,
         (∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) * X.drift) →
         Tendsto (fun n => max (F n ω - (w 0 + L n ω)) 0) atTop (𝓝 (0 : ℝ)))) := by sorry
