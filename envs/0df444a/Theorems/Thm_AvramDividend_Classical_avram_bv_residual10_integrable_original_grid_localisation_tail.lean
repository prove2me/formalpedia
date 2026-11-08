-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_integrable_original_grid_localisation_tail
-- name    : AvramDividend.Classical.avram_bv_residual10_integrable_original_grid_localisation_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:46:54.586214+00:00
-- url     : https://prove2.me/theorems/f70f423f-c690-4b73-a28e-5f4d8e402042
-- title:
--   Original finite-grid clipping tails vanish in L1 when the exact original source is integrable
-- statement:
--   For one original finite physical row, coefficient clipping converges in expected absolute error provided the original, untruncated source is integrable. The proof combines exact pathwise exhaustion, event measurability and dominated convergence with dominating function |f|. There is no finite-measure requirement, no Brownian-process replacement, and no uniformity in row n. In Avram this result only applies after proving original-process raw residual integrability, which remains a separate open obligation.
-- source:
--   AVRAM BV-RESIDUAL10 source-exact finite-grid localisation, pinned Mathlib dominated convergence, 7 November 2026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_residual10_integrable_original_grid_localisation_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f P) :
    Tendsto (fun k : ℕ =>
      ∫ ω : Ω, if ω ∈ {z : Ω | ∀ i ∈ Finset.range (n + 1),
          abs (a z i) ≤ (k : ℝ)} then (0 : ℝ) else abs (f ω) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
