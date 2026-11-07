-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_uniform_clipped_grid_monotone_eventual_raw
-- name    : AvramDividend.Classical.avram_bv_gen8_original_uniform_clipped_grid_monotone_eventual_raw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:57:18.837838+00:00
-- url     : https://prove2.me/theorems/9c361280-4e93-4d7c-969e-bf4452df4237
-- title:
--   Original BV grid generator clipping is antitone in cutoff and eventually equals raw grid pathwise
-- statement:
--   For the exact stopped BV generator physical grid, clipping max(-K,H_i) decreases pointwise as the real cutoff K increases, and a natural cutoff eventually removes all clipping for each fixed outcome and finite grid. This imports the accepted pathwise cutoff certificate 8a693f60 and prepares the monotone one-sided limiting argument without asserting raw L1.
-- source:
--   Order monotonicity of max in the cutoff plus accepted 8a693f60 eventual raw equality.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_uniform_clipped_grid_eventually_raw
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_uniform_clipped_grid_monotone_eventual_raw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (ω : Ω) (K L : ℝ) (hKL : K ≤ L) :
    let Z : ℕ → ℝ := fun j => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
    let H : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    (∑ i ∈ Finset.range (n + 1), max (-L) (H i)) ≤
      (∑ i ∈ Finset.range (n + 1), max (-K) (H i)) ∧
      ∃ N : ℕ, ∀ M ≥ N,
        (∑ i ∈ Finset.range (n + 1), max (-(M : ℝ)) (H i)) =
          ∑ i ∈ Finset.range (n + 1), H i := by sorry
