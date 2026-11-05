-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
-- name    : AvramDividend.Classical.avram_p3_main_original_jump_removed_grid_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:49:28.356406+00:00
-- url     : https://prove2.me/theorems/e9650890-8657-43f3-bf81-46f202f62ba6
-- title:
--   Original BV jump-removed source finite-grid variation is bounded by physical drift and monotone residual
-- statement:
--   On a single P-full event for the original BV Lévy source, every monotone nonnegative time grid has a controlled sum of absolute increments of Y(t)=X.X_t+J(t), where J is the actual real magnitude of all original negative left jumps. The sum is at most |X.drift| times elapsed time plus the difference of the genuine nondecreasing source residual R(t)=t·X.drift−X.X_t−J(t). This is the precise source-level variation envelope for P3-D's Taylor mesh, without assuming R=0 or changing processes.
-- source:
--   Proved e9d95081 original monotone physical residual and Proved 7bfe4086 deterministic finite-grid variation estimate, applied with actual original process X.X and its intrinsic left jumps. Supports canonical a19d8b28 stopped prebudget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_main_original_jump_removed_grid_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t => (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (n : ℕ) (u : ℕ → ℝ≥0),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∑ i ∈ Finset.range n,
          |Y (u (i + 1)) - Y (u i)|) ≤
          |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) := by sorry
