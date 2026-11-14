-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb78_original_true_T_survivor_discounted_terminal_uniform_grid_left_limit
-- name    : AvramDividend.Classical.avram_bvb78_original_true_T_survivor_discounted_terminal_uniform_grid_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:43:24.071695+00:00
-- url     : https://prove2.me/theorems/e929c759-8d45-4548-819f-94f4363c99e7
-- title:
--   Original stopped discounted BV candidate terminal reward converges at true physical horizon along any left cofinal mesh
-- statement:
--   The genuine discounted stopped candidate reward converges almost surely along any discrete left-directed physical clock to the actual full-T survivor terminal reward, by composing the already Proved original killed terminal left-continuity theorem. Useful to pass from T-delta_n to exact physical T in BVB76 while preserving actual ruinTime and D.
-- source:
--   Proved a9b3240d-cc23-4b2f-86a1-d28e77b12ef5; original BVB76 true-T survivor branch

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb78_original_true_T_survivor_discounted_terminal_uniform_grid_left_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (q : ℝ)
    (t : ℝ≥0) (ht : 0 < t)
    (u : ℕ → ℝ≥0) (hu : Tendsto u atTop (𝓝[<] t)) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun n =>
        if (u n : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * ((u n) : ℝ))) * w (riskProcess X x D (u n) ω) else 0)
        atTop
        (𝓝 (Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω))) := by sorry
