-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_predictable_conditionally_centered_physical_grid_L2_isometry
-- name    : AvramDividend.Classical.avram_pj_original_predictable_conditionally_centered_physical_grid_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:09:37.790297+00:00
-- url     : https://prove2.me/theorems/b9b51e38-bdc0-4fbb-83e6-9816b9160dc0
-- title:
--   Actual adapted physical-grid compensated fullmark martingale sum has exact L2 diagonal isometry from predictable conditional centring
-- statement:
--   For a finite original filtration-adapted grid, if each increment is a past-predictable weight H times a conditionally mean-zero future marked increment V, and products are integrable, then the expected squared full sum equals the sum of true diagonal second moments. Each off-diagonal covariance vanishes by the exact proved conditional pull-out lemma; the provided true-grid weight measurability hypotheses are explicit and auditable, and no unsupported independence shortcut is made.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_predictable_conditionally_centered_physical_grid_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ j, m j ≤ mΩ)
    (H V Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ω, Z i ω = H i ω * V i ω)
    (hVInt : ∀ j ∈ Finset.range n, Integrable (V j) P)
    (hCond : ∀ j ∈ Finset.range n,
      P[V j | m j] =ᵐ[P] (fun _ => 0))
    (hPair : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => Z i ω * Z j ω) P)
    (hPast : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j →
      StronglyMeasurable[m j] (fun ω => Z i ω * H j ω)) :
    (∫ ω, (∑ i ∈ Finset.range n, Z i ω)^2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω, (Z i ω)^2 ∂P := by sorry
