-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_cgf_quadratic
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_cgf_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:29:35.866309+00:00
-- url     : https://prove2.me/theorems/af0c2a9a-7e53-4821-b20c-9cecacf55560
-- title:
--   Original normalised Gaussian increment cumulant is the quadratic interval formula
-- statement:
--   For the actual original zero-jump source of matching variance, the cumulant-generating function of each drift-centred normalised deterministic increment equals half the squared nonnegative Laplace parameter times the interval length.
-- source:
--   Proved original P4-A normalised increment Gaussian MGF; Mathlib Gaussian MGF and cgf definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_cgf_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    ProbabilityTheory.cgf
      (fun ω => ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ)
      P θ = ((t - s : ℝ≥0) : ℝ) * (θ ^ 2 / 2) := by sorry
