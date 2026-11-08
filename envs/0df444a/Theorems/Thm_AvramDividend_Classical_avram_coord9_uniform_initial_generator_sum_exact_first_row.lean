-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord9_uniform_initial_generator_sum_exact_first_row
-- name    : AvramDividend.Classical.avram_coord9_uniform_initial_generator_sum_exact_first_row
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:17:01.852938+00:00
-- url     : https://prove2.me/theorems/6af146c4-53d3-4dbd-97dd-0034f4fee696
-- title:
--   Original uniform physical-grid first generator row reduces to the literal half-horizon source cell
-- statement:
--   At grid level zero, the exact source formula for the signed generator sum has one cell. The prescribed uniform endpoints zero and T/2 reduce it to the initial left-limit generator source times T/2 with the original survival, positivity, and cap indicators. The compensated clock correction is unchanged.
-- source:
--   COORD9 exact first-row generator source extraction from the original stopped-grid B definition, 7 November 2026.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_coord9_uniform_initial_generator_sum_exact_first_row
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (B : ℕ → Ω → ℝ) (K : Ω → ℝ)
    (hzero : u 0 0 = 0)
    (hone : (u 0 1 : ℝ) = T / 2)
    (hBraw : ∀ ω, B 0 ω =
      (let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u 0 i)
       ∑ i ∈ Finset.range (0 + 1),
         if (u 0 i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z i ∧ ENNReal.ofReal (Z i) < C then
           Real.exp (-(q * (u 0 i : ℝ))) *
             (X.generator w (Z i) - q * w (Z i)) *
             ((u 0 (i + 1) : ℝ) - (u 0 i : ℝ))
         else 0) + K ω) :
    ∀ ω, B 0 ω =
      (let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
       if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z ∧ ENNReal.ofReal Z < C then
         Real.exp (-(q * (0 : ℝ))) *
           (X.generator w Z - q * w Z) * (T / 2)
       else 0) + K ω := by sorry
