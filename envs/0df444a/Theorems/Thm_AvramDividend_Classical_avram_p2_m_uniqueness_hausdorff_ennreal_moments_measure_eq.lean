-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_hausdorff_ennreal_moments_measure_eq
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_hausdorff_ennreal_moments_measure_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:11:54.411837+00:00
-- url     : https://prove2.me/theorems/4bf8ed6c-17fc-4952-9cb2-b3e703805a7c
-- title:
--   Hausdorff uniqueness of finite regular unit measures from all ENNReal power moments
-- statement:
--   Two finite regular measures almost everywhere on [0,1] with finite ENNReal monomial moments, integrable real powers and equal ENNReal moments of every order are equal on all Borel sets, including endpoint atoms. Convert the constant-sequence ENNReal moment limits to real moments by the Proved P2-I theorem and apply the separately owned P2-M real Hausdorff measure uniqueness theorem. This is full measure determinacy and does not assume the desired measure equality or exclude endpoints.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_hausdorff_ennreal_moments_measure_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular]
    (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hν : ∀ᵐ z ∂ν, z ∈ Set.Icc (0 : ℝ) 1)
    (hmonoμ : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) μ)
    (hmonoν : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) ν)
    (hfiniteν : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν) ≠ ⊤)
    (hmom : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)) :
    μ = ν := by sorry
