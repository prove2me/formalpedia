-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_true_physical_positive_ito_excess_dominated_ae_vanish_implies_L1
-- name    : AvramDividend.Classical.avram_pj_true_physical_positive_ito_excess_dominated_ae_vanish_implies_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T17:46:25.65284+00:00
-- url     : https://prove2.me/theorems/4e3a6978-e918-4d2d-80b2-a1a1a0abb417
-- title:
--   Dominated genuine physical-grid positive stochastic Ito excess vanishing almost everywhere implies L1 convergence
-- statement:
--   If a sequence F_k of integrable genuine original stopped physical-grid stochastic Ito signed upper errors converges pointwise to zero almost everywhere and is bounded in absolute value by a single integrable original-path random variable B, then its absolute expected value converges to zero. Applies Mathlib Bochner dominated convergence to the absolute errors, preserving exact original physical-grid stopping, full negative-mark compensator and Stieltjes dividend correction when instantiated by the original positive-part residual of source 35e57d4e. This isolates the mathematically difficult pathwise Ito identification and integrable domination obligations from the elementary L1 convergence bridge.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_true_physical_positive_ito_excess_dominated_ae_vanish_implies_L1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ)
    (hFI : ∀ k, Integrable (F k) P)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, |F k ω| ≤ B ω)
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => ∫ ω, |F k ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
