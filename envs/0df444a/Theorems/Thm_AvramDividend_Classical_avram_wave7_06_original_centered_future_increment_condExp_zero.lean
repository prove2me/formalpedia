-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_centered_future_increment_condExp_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_centered_future_increment_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:49:22.369197+00:00
-- url     : https://prove2.me/theorems/c1a8a389-dfd2-42de-957c-42fe5b63dfc9
-- title:
--   Mean-centred original future Levy increment has zero conditional expectation given source filtration
-- statement:
--   For the canonical Levy X, the original-filtration conditional expectation of the future increment minus its source expectation is zero. Requires integrability, the actual independence field and existing proved source mean and conditional-expectation identities; no auxiliary process.
-- source:
--   W7-06 original stopped martingale precursor, source-specific conditional mean.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_centered_future_increment_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (X.X t) P) :
    P[(fun ω => (X.X (s + t) ω - X.X s ω) -
      (∫ η, X.X t η ∂P)) | 𝓕 s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by sorry
