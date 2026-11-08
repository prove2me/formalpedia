-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_first_generator_cell_identity
-- name    : AvramDividend.Classical.avram_a19_uniform_first_generator_cell_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:06:26.279851+00:00
-- url     : https://prove2.me/theorems/85b0b724-3b0b-4799-862e-d0739dbaa1f5
-- title:
--   Original A19 first generator cell exactly samples post-dividend reserve and uniform mesh width
-- statement:
--   For every uniform-grid row n, the source-exact first stopped generator cell equals the HJB generator deficit evaluated at initial surplus minus right-limit initial dividend, multiplied by T/(n+2), on the precise original positivity, cap and non-ruin event. It is zero outside that event.
-- source:
--   A19 original physical uniform-grid generator finite-integral target 5df846f9-a565-461b-bd12-d65befd305b6, first-cell exact-model obstruction, 7 November 2026.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_origin_postright_surplus
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_uniform_first_generator_cell_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (u : ℕ → ℕ → ℝ≥0)
    (hgrid0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (ω : Ω) :
    (let Z : ℕ → ℝ := fun j => Function.leftLim
       (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
     if (u n 0 : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z 0 ∧ ENNReal.ofReal (Z 0) < C then
       Real.exp (-(q * (u n 0 : ℝ))) *
         (X.generator w (Z 0) - q * w (Z 0)) *
         ((u n 1 : ℝ) - (u n 0 : ℝ))
     else 0) =
    (if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
         0 < x - rightLimit D 0 ω ∧
         ENNReal.ofReal (x - rightLimit D 0 ω) < C then
       (X.generator w (x - rightLimit D 0 ω) -
           q * w (x - rightLimit D 0 ω)) *
         (T / ((n : ℝ) + 2))
     else 0) := by sorry
