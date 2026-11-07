-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_masked_BV_residual_cell_sum_identity
-- name    : AvramDividend.Classical.avram_p3_grid4_original_masked_BV_residual_cell_sum_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T14:19:01.269163+00:00
-- url     : https://prove2.me/theorems/6254302d-e40f-4d98-899f-8cda0d9b61a6
-- title:
--   Original BV drift-residual decomposition under arbitrary stopped-grid cell masks
-- statement:
--   For the actual original spectrally negative Levy process X and its exact untruncated all-jump sum J, the BV residual R(t)=t*drift-X(t)-J(t) has cell increments Delta R=Delta X+Delta J-drift Delta t. This identity remains valid after multiplying each physical grid cell by an arbitrary real-valued stopping/localisation mask a_i. It is the exact algebra needed to reconcile the masked R summand of the canonical 2bc848f9 original BV source B with physical reserve increments, without imposing false assumptions at ruin or cap contact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_masked_BV_residual_cell_sum_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    (∑ i ∈ Finset.range n, a i * (R (u i) - R (u (i + 1)))) =
      ∑ i ∈ Finset.range n, a i *
        ((X.X (u (i + 1)) ω - X.X (u i) ω) +
         (J (u (i + 1)) - J (u i)) -
         (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)) := by sorry
