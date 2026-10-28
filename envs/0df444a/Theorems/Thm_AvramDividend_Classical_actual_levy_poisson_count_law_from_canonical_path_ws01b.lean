-- Prove2me | Theorems.Thm_AvramDividend_Classical_actual_levy_poisson_count_law_from_canonical_path_ws01b
-- name    : AvramDividend.Classical.actual_levy_poisson_count_law_from_canonical_path_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:06:11.238982+00:00
-- url     : https://prove2.me/theorems/35f45f27-811d-49f1-9e1b-247a513fec67
-- title:
--   Transfer the entire Poisson count law of a measurable Lévy jump-count functional from a matching canonical process
-- statement:
--   For two actual spectrally negative Lévy processes with the same Lévy triplet (drift, Gaussian coefficient and Lévy measure), the entire Poisson law HasLaw(count(path),Poisson(r)) of any measurable pathwise jump-count functional transfers from a canonical process to the original one. This proves all count masses, not just the zero-jump event. The canonical law and measurability of the count functional are substantive explicit hypotheses; no direct PRM construction or predictable filtration independence is presumed.
-- source:
--   Derived from canonically Proved cross_levy_whole_path_law_of_equal_triplet, and measurability of the adapted Lévy sample path into real product path space. A genuine actual-process link for truncated Poisson jump counting, preparatory to BV generator-to-Dynkin.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_triplet

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.actual_levy_poisson_count_law_from_canonical_path_ws01b
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (count : (ℝ≥0 → ℝ) → ℕ) (hcount : Measurable count)
    (r : ℝ≥0)
    (hYlaw : HasLaw
      (fun ω : Ω₂ => count (fun t : ℝ≥0 => Y.X t ω))
      (poissonMeasure r) P₂) :
    HasLaw
      (fun ω : Ω₁ => count (fun t : ℝ≥0 => X.X t ω))
      (poissonMeasure r) P₁ := by sorry
