-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_positive_event_surviving_nonzero_ruin_refutes_original_ae_limit
-- name    : AvramDividend.Classical.avram_bvb_obstruction_positive_event_surviving_nonzero_ruin_refutes_original_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:50:13.437729+00:00
-- url     : https://prove2.me/theorems/f4d76cbd-428b-404b-9d16-3fc2c7ba354a
-- title:
--   Positive-probability nonzero-ruin event with persistent discounted cash excess refutes original a.e. stopped positive-part limit
-- statement:
--   If a positive-probability event guarantees a nonzero ruin time and failure of the positive-part error to tend to zero, then the original stopped physical-grid error, including its conditional zero-ruin branch, cannot converge to zero almost everywhere. This is the exact logical endpoint needed to formally refute the zero-contact survivor branch.
-- source:
--   The original a.e. convergence claim implies its failure set has zero measure. Every sample in the positive nonzero-ruin counterexample event lies in that failure set, contradicting measure monotonicity.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_obstruction_positive_event_surviving_nonzero_ruin_refutes_original_ae_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (τ : Ω → ℝ≥0∞) (A : ℕ → Ω → ℝ)
    (hPositive : 0 < P E)
    (hSurvive : ∀ ω ∈ E, τ ω ≠ 0)
    (hBad : ∀ ω ∈ E,
      ¬ Tendsto (fun n => max (A n ω) 0) atTop (𝓝 (0 : ℝ))) :
    ¬ (∀ᵐ ω ∂P, Tendsto
      (fun n => if τ ω = 0 then 0 else max (A n ω) 0)
      atTop (𝓝 (0 : ℝ))) := by sorry
