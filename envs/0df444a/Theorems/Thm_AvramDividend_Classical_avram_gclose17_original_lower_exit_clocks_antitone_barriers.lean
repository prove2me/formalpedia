-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_lower_exit_clocks_antitone_barriers
-- name    : AvramDividend.Classical.avram_gclose17_original_lower_exit_clocks_antitone_barriers
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:16:12.075579+00:00
-- url     : https://prove2.me/theorems/27d46f1e-2610-47b8-a013-3aefec641d17
-- title:
--   Original sampled lower-exit clocks increase as reserve thresholds decrease
-- statement:
--   For any actual original Levy reserve path and every decreasing sequence of real lower barriers, the first sampled lower exits, clipped under a fixed original clock, are increasing in the barrier index. This is a deterministic pathwise order theorem required to turn the supremum stopping clock into an increasing first-zero-contact candidate and to use exact cofinal strict reward endpoint convergence. It imposes no hypothetical Ito or martingale assumption.
-- source:
--   Pointwise inclusion of threshold-violation events and order of infimum clocks; no filtration substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose17_original_lower_exit_clocks_antitone_barriers
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → WithTop ℝ≥0) (r : ℕ → ℝ≥0)
    (δ : ℕ → ℝ) (hδ : Antitone δ) :
    ∀ ω, Monotone (fun n : ℕ =>
      min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤)) := by sorry
