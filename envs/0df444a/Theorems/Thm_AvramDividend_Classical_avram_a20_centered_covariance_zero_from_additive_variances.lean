-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_centered_covariance_zero_from_additive_variances
-- name    : AvramDividend.Classical.avram_a20_centered_covariance_zero_from_additive_variances
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T09:56:37.584631+00:00
-- url     : https://prove2.me/theorems/2bab63a4-d79d-4349-a158-1bb676f0a38c
-- title:
--   Centred covariance vanishes when three square moments and the additive union agree
-- statement:
--   For any three real random functions A, B, U on a common measure space whose union process U equals A+B almost surely, if the three square integrals exist and the square integral of U equals the sum of those of A and B, then AB is integrable and its integral vanishes. The integrability of AB follows algebraically from the three given integrable squares, requiring no extra measurability assumption on A or B. This is the algebraic physical-cell covariance reduction used in the Avram original jump-noise mission.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a20_centered_covariance_zero_from_additive_variances
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B U : Ω → ℝ) (rA rB : ℝ)
    (hA : Integrable (fun ω => (A ω) ^ 2) P)
    (hB : Integrable (fun ω => (B ω) ^ 2) P)
    (hU : Integrable (fun ω => (U ω) ^ 2) P)
    (hAdd : ∀ᵐ ω ∂P, U ω = A ω + B ω)
    (hMeanA : (∫ ω, (A ω) ^ 2 ∂P) = rA)
    (hMeanB : (∫ ω, (B ω) ^ 2 ∂P) = rB)
    (hMeanU : (∫ ω, (U ω) ^ 2 ∂P) = rA + rB) :
    Integrable (fun ω => A ω * B ω) P ∧
      (∫ ω, A ω * B ω ∂P) = 0 := by sorry
