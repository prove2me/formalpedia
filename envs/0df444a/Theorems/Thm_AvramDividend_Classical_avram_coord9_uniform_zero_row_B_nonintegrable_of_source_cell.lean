-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord9_uniform_zero_row_B_nonintegrable_of_source_cell
-- name    : AvramDividend.Classical.avram_coord9_uniform_zero_row_B_nonintegrable_of_source_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:55:48.136598+00:00
-- url     : https://prove2.me/theorems/eb58ac18-5114-4419-b621-67ad01a3f6fc
-- title:
--   Original uniform zero-row signed residual inherits a nonintegrable source generator cell
-- statement:
--   When the zero row of a source-exact uniform physical-grid residual equals the initial generator cell plus an integrable compensated clock correction, nonintegrability of the initial profile precludes integrability of the signed residual on that row. Its first-cell statement is retained literally, and the compensated correction remains a separate process-specific obligation.
-- source:
--   COORD9 7 November 2026 exact zero-row source residual bridge for the uniform BV route, requiring the original first-row equality and an integrable compensated clock correction.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_coord9_original_zero_uniform_cell_nonintegrable_of_profile
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_coord9_uniform_zero_row_B_nonintegrable_of_source_cell
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
    (B : ℕ → Ω → ℝ) (K : Ω → ℝ)
    (hB0 : ∀ ω, B 0 ω =
      (let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
       if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z ∧ ENNReal.ofReal Z < C then
         Real.exp (-(q * (0 : ℝ))) *
           (X.generator w Z - q * w Z) * (T / 2)
       else 0) + K ω)
    (hK : Integrable K P) : ¬ Integrable (B 0) P := by sorry
