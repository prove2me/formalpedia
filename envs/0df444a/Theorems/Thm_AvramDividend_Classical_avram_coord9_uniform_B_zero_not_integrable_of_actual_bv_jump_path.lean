-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord9_uniform_B_zero_not_integrable_of_actual_bv_jump_path
-- name    : AvramDividend.Classical.avram_coord9_uniform_B_zero_not_integrable_of_actual_bv_jump_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:15:45.570593+00:00
-- url     : https://prove2.me/theorems/75eba433-9d50-4c1e-8f89-d230f64f4864
-- title:
--   Original uniform-grid zero residual is nonintegrable under the genuine BV jump-path identity and singular source profile
-- statement:
--   The actual drift-minus-jump path identity makes the original row-zero compensated clock sum identically zero. An exact first-row generator identity and a measurable but nonintegrable initial HJB profile then imply nonintegrability of the signed source residual at n zero. The original-process existence and source-specialisation assumptions are explicit.
-- source:
--   COORD9 downstream Lean integration of two accepted conditional source-exact helper proofs, 7 November 2026.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_coord9_bv_original_clock_correction_zero_of_jump_path
import Theorems.Thm_AvramDividend_Classical_avram_coord9_uniform_zero_row_B_nonintegrable_of_source_cell
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_coord9_uniform_B_zero_not_integrable_of_actual_bv_jump_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T x : ℝ) (hT : 0 < T)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hruin : ∀ ω, (0 : ℝ≥0∞) < ruinTime X x D ω)
    (hpositive : ∀ ω, 0 < x - rightLimit D 0 ω)
    (hcap : ∀ ω, ENNReal.ofReal (x - rightLimit D 0 ω) < C)
    (hmeas : AEStronglyMeasurable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (hnonint : ¬ Integrable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (u : ℕ → ℕ → ℝ≥0) (B : ℕ → Ω → ℝ) (K : Ω → ℝ)
    (hpath : ∀ (ω : Ω) (t : ℝ≥0),
      ((t : ℝ) * X.drift - X.X t ω) =
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
    (hK_def : ∀ ω, K ω =
      (let Z : ℕ → ℝ := fun i => Function.leftLim
         (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u 0 i)
       let J : ℝ≥0 → ℝ := fun t =>
         ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
           Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (0 + 1),
         (if (u 0 i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u 0 i : ℝ))) * deriv w (Z i)
          else 0) * (R (u 0 i) - R (u 0 (i + 1)))))
    (hB0 : ∀ ω, B 0 ω =
      (let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
       if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z ∧ ENNReal.ofReal Z < C then
         Real.exp (-(q * (0 : ℝ))) *
           (X.generator w Z - q * w Z) * (T / 2)
       else 0) + K ω) :
    ¬ Integrable (B 0) P := by sorry
