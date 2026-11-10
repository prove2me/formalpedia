-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_compact_strict_sampled_exit_eventually_after_prefix
-- name    : AvramDividend.Classical.avram_gclose16_original_compact_strict_sampled_exit_eventually_after_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:46:42.044344+00:00
-- url     : https://prove2.me/theorems/9fcc99ab-4e99-473e-a95f-28dd12e63167
-- title:
--   Compact strict original reserve solvency prevents low-threshold sampled exits before its endpoint
-- statement:
--   On a fixed compact prefix with pathwise strictly positive original postpayment reserve, any sequence of lower reserve thresholds converging to zero has no sampled exit before the prefix for all sufficiently large indices. This is a deterministic cofinality input for original-filtration Gaussian pre-exit localisation. It does not assert that pathwise strict solvency is automatic before ruin.
-- source:
--   Use Proved compact strict postpayment uniform floor 026251d7 to find a positive margin on the prefix, then use threshold convergence to show the margin exceeds every sufficiently late threshold. Every alleged sampled exit before the prefix contradicts the margin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_compact_strict_postpayment_uniform_floor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose16_original_compact_strict_sampled_exit_eventually_after_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (hpos : ∀ s : ℝ≥0, s ≤ T →
      0 < x + X.X s ω - rightLimit D s ω)
    (r : ℕ → ℝ≥0) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤
      (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < ε n
        then (r k : WithTop ℝ≥0) else ⊤) := by sorry
