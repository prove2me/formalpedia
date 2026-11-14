-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_difference_variance_of_self_covariance_20261113
-- name    : AvramDividend.Classical.avram_a21_original_difference_variance_of_self_covariance_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:43:40.251174+00:00
-- url     : https://prove2.me/theorems/62a65763-40ed-478e-86df-b2488b303063
-- title:
--   Original difference variance after exact retained-jump self covariance
-- statement:
--   When a retained centred jump variable has original covariance equal to its own second moment with zero-cutoff residual, subtracting it removes exactly its variance.
-- source:
--   Pinned Mathlib Bochner integral linearity and real ring normalization; true Gaussian cutoff variance reduction avoiding false original independence.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_difference_variance_of_self_covariance_20261113
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : Ω → ℝ)
    (hU : Integrable (fun ω => (U ω)^2) P)
    (hV : Integrable (fun ω => (V ω)^2) P)
    (hUV : Integrable (fun ω => U ω * V ω) P)
    (hCov : (∫ ω, U ω * V ω ∂P) = (∫ ω, (V ω)^2 ∂P)) :
    Integrable (fun ω => (U ω - V ω)^2) P ∧
      (∫ ω, (U ω - V ω)^2 ∂P) =
        (∫ ω, (U ω)^2 ∂P) - (∫ ω, (V ω)^2 ∂P) := by sorry
