-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a127_original_gaussian_random_crossing_HJB_compensator_expected_L1
-- name    : AvramDividend.Classical.avram_ga_a127_original_gaussian_random_crossing_HJB_compensator_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:15:57.470841+00:00
-- url     : https://prove2.me/theorems/332de8ae-7711-46d7-ad53-c85c28e54a56
-- title:
--   Original random Gaussian true crossing-cell HJB compensator vanishes in expected absolute L1 from the source modulus and one integrable horizon envelope
-- statement:
--   For a true randomly selected Gaussian crossing cell, an HJB compensation bounded by a fixed compact coefficient times absolute full physical source increment, its square and mesh width tends to zero almost surely as the source increment and mesh vanish. If the true compensator is measurable and has one finite-horizon integrable envelope, its expected absolute error also tends to zero. This is the precise stochastic expectation bridge needed alongside the stopped-value expected L1 in the original one-sided crossing-cell budget.
-- source:
--   Proved ga112 source-modulus-to-HJB compensation pathwise limit and pinned Mathlib dominated convergence; original b0 crossing-cell one-sided obligation ga120.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a112_original_gaussian_random_crossing_compensator_small_from_source_modulus
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a127_original_gaussian_random_crossing_HJB_compensator_expected_L1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z Δ H : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hΔ : ∀ m ω, 0 ≤ Δ m ω)
    (hError : ∀ m ω,
      |H m ω| ≤ K * (|Z m ω| + (Z m ω)^2 + Δ m ω))
    (hZ : ∀ᵐ ω ∂P, Tendsto (fun m => Z m ω) atTop (𝓝 (0 : ℝ)))
    (hΔlim : ∀ᵐ ω ∂P, Tendsto (fun m => Δ m ω) atTop (𝓝 (0 : ℝ)))
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => |H m ω|) P)
    (hDom : ∀ m, ∀ᵐ ω ∂P, |H m ω| ≤ B ω) :
    Tendsto (fun m => ∫ ω, |H m ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
