-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18k_subsigma_dominated_ae_limit_meas
-- name    : AvramDividend.Classical.avram_ja18k_subsigma_dominated_ae_limit_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:06:58.393768+00:00
-- url     : https://prove2.me/theorems/f6c3e9f6-a591-4fe0-9883-3cd3845b930c
-- title:
--   A dominated almost-sure limit of sub-sigma-algebra AE-measurable real variables remains sub-sigma-algebra AE-measurable
-- statement:
--   For an arbitrary original measure and a coarser sigma algebra, if the original-space random variables are each almost-everywhere strongly measurable for the coarser sigma algebra, converge almost surely, and admit a common integrable real norm envelope, show that the limit is also almost-everywhere strongly measurable for that same coarser sigma algebra. This is a standard closed-subspace theorem in L1; use Mathlib isClosed_aestronglyMeasurable and dominated L1 convergence, keeping the original measure. No original Lévy process or auxiliary probability space needed.
-- source:
--   Sound generic analytic child of Avram JA18 adaptedness theorem ed4dbe1a, needed to close original bounded-band stopped compensation.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18k_subsigma_dominated_ae_limit_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (hSub : m ≤ mΩ)
    (f : ℕ → Ω → ℝ) (g B : Ω → ℝ)
    (hMeas : ∀ n : ℕ, AEStronglyMeasurable[m] (f n) P)
    (hBi : Integrable B P)
    (hBound : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (g ω))) :
    AEStronglyMeasurable[m] g P := by sorry
