-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_X_condExp_source_past_eq_Xpast_plus_mean
-- name    : AvramDividend.Classical.avram_wave7_06_original_future_X_condExp_source_past_eq_Xpast_plus_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:02:38.934503+00:00
-- url     : https://prove2.me/theorems/a49a3ceb-6581-4d80-a7c3-8cbee39239d6
-- title:
--   Canonical Levy X conditional future state equals its original past plus source increment mean
-- statement:
--   For integrable original X_s and X_t, conditional expectation of actual X_(s+t) given original 𝓕_s equals X_s + E[X_t]. Uses true X.adapted filtration measurability, original future independent increments, and pinned condExp_add and condExp_of_stronglyMeasurable; source process and P unchanged. This is the drift-adjusted source martingale step.
-- source:
--   W7-06 full original-filtration source conditional martingale identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_future_X_condExp_source_past_eq_Xpast_plus_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hStart : Integrable (X.X s) P)
    (hFuture : Integrable (X.X t) P) :
    P[X.X (s + t) | 𝓕 s] =ᵐ[P]
      (fun ω => X.X s ω + (∫ η, X.X t η ∂P)) := by sorry
