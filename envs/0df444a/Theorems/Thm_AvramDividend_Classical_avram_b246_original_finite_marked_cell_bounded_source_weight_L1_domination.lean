-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b246_original_finite_marked_cell_bounded_source_weight_L1_domination
-- name    : AvramDividend.Classical.avram_b246_original_finite_marked_cell_bounded_source_weight_L1_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:24:41.772503+00:00
-- url     : https://prove2.me/theorems/e84cc2af-bb74-4a59-a9f3-53da5ace03ff
-- title:
--   Canonical finite random marked-cell bounded weights have integrable signed sum dominated pathwise by weight bound times original marked-cell count
-- statement:
--   For any measurable signed total over the finite random marked physical cells of the original finite-activity Lévy path, if their count is integrable and every active cell source weight has norm at most a common nonnegative bound L, then the signed total is integrable and its absolute value is at most L times the marked-cell count on every path. Applied with B243 original canonical marked-cell L1 count dominated by true negative jump Poisson marks, this is the marked source energy domination step for B236 actual ruin-clipped physical grid and the negative-mark Ito cash Taylor residual. The theorem explicitly assumes strong measurability of the signed marked total and avoids assuming measurability of every random marked cell index.
-- source:
--   Finite triangle inequality and pointwise bound sum over the actual finite marked set, followed by integrability domination via the integrable nonnegative marked-cell count. No after-ruin trajectory or circular Gaussian assumption.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b246_original_finite_marked_cell_bounded_source_weight_L1_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (marked : Ω → Finset ℕ)
    (hCount : Integrable (fun ω => ((marked ω).card : ℝ)) P)
    (W : Ω → ℕ → ℝ)
    (hMeas : AEStronglyMeasurable
      (fun ω => ∑ i ∈ marked ω, W ω i) P)
    (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ ω i, i ∈ marked ω → ‖W ω i‖ ≤ L) :
    Integrable (fun ω => ∑ i ∈ marked ω, W ω i) P ∧
    ∀ ω, ‖∑ i ∈ marked ω, W ω i‖ ≤
      L * ((marked ω).card : ℝ) := by sorry
