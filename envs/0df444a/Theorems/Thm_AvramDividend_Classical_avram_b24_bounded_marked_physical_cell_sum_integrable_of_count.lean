-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_bounded_marked_physical_cell_sum_integrable_of_count
-- name    : AvramDividend.Classical.avram_b24_bounded_marked_physical_cell_sum_integrable_of_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:32:10.247869+00:00
-- url     : https://prove2.me/theorems/69ed175e-3ce8-4e77-808d-cdd3d26388c8
-- title:
--   Finite marked-cell weighted sum is integrable when the count is integrable and individual weights are uniformly bounded
-- statement:
--   For the actual original finite-activity physical stopped marked cells, any measurable finite sum of real coefficients bounded uniformly in absolute value is integrable whenever the number of selected marked cells has finite first moment. It gives the direct L1 marked-jump domination bridge from the Proved canonical marked-cell counting theorem to the Ito jump remainder.
-- source:
--   Proved B243 original true ruin-clipped marked-cell count L1, Proved B207 canonical bounded marked-grid source, elementary finite norm-sum bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_b24_bounded_marked_physical_cell_sum_integrable_of_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (marked : Ω → Finset ℕ)
    (hCount : Integrable (fun ω => ((marked ω).card : ℝ)) P)
    (W : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hW : ∀ i ω, |W i ω| ≤ L)
    (hMeas : AEStronglyMeasurable
      (fun ω => ∑ i ∈ marked ω, W i ω) P) :
    Integrable (fun ω => ∑ i ∈ marked ω, W i ω) P := by sorry
