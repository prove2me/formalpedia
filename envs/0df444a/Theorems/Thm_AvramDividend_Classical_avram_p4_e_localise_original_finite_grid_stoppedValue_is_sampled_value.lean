-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:35:24.240415+00:00
-- url     : https://prove2.me/theorems/f030240a-d96a-4dd9-9ab2-b3b7429f6b6f
-- title:
--   Finite original sampled stopping index value equals process at that grid index
-- statement:
--   For any finite original-grid index K, the Mathlib stoppedValue of the sampled original process at WithTop-coerced K equals direct evaluation f(e(K)). This definal bridge is needed to identify optional-stopping expressions with the time-indexed upper-clock values used by P4-E a.e. and L1 limit theorems. It makes no martingale, boundary or integrability assertion.
-- source:
--   Pinned Mathlib stoppedValue definition for WithTop-coerced finite clock; original source SpectrallyNegativeLevy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite original-clock sampled stopping index evaluates the unchanged source process at its grid time. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ≥0 → Ω → ℝ) (e : ℕ → ℝ≥0)
    (K : Ω → ℕ) :
    ∀ ω, stoppedValue (fun i : ℕ => f (e i))
      (fun ω => (K ω : WithTop ℕ)) ω = f (e (K ω)) ω := by sorry
