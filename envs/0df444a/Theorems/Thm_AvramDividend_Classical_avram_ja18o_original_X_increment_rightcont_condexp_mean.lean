-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18o_original_X_increment_rightcont_condexp_mean
-- name    : AvramDividend.Classical.avram_ja18o_original_X_increment_rightcont_condexp_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:29:48.311114+00:00
-- url     : https://prove2.me/theorems/281f0616-8aee-451c-b678-db991d07c2b1
-- title:
--   Original Lévy future increment has deterministic conditional mean under right-continuous filtration
-- statement:
--   For an integrable original Lévy increment X(t)-X(s), prove its conditional expectation under the original right-continuous filtration at s equals its unconditional mean. The original shifted path is independent of that past, and evaluation at t-s is a measurable factor. This supplies the actual X-centred right-continuous martingale with no auxiliary coupling.
-- source:
--   JA18N rightCont X centred martingale

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18o_original_X_increment_rightcont_condexp_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hXs : Integrable (X.X s) P) (hXt : Integrable (X.X t) P) :
    condExp (𝓕.rightCont s) P
      (fun ω => X.X t ω - X.X s ω) =ᵐ[P]
    (fun _ : Ω => ∫ η, X.X t η - X.X s η ∂P) := by sorry
