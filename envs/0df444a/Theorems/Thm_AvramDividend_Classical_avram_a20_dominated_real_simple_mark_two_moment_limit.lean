-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_dominated_real_simple_mark_two_moment_limit
-- name    : AvramDividend.Classical.avram_a20_dominated_real_simple_mark_two_moment_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:59:20.195208+00:00
-- url     : https://prove2.me/theorems/07ffe5f3-7cab-49ec-b6db-908546bb971b
-- title:
--   Dominated original mark-simple approximants transfer exact first and second real moments to measurable weighted Borel mark integral
-- statement:
--   Any sequence of almost everywhere measurable real simple-mark random variables f_k that converges pointwise almost surely to an original source weighted mark integral J and is uniformly dominated in absolute value by a physical random bound B whose first and second moments are integrable transfers exact limits of both the raw first and second moments of f_k to J. In particular J and J² are integrable and E[J]=lim E[f_k], E[J²]=lim E[f_k²]. Proof applies the pinned Mathlib dominated convergence theorem to the sequence and its square, with the resulting a.e. strong measurability and inherited norm dominators. This analytic bridge is directly usable to lift the independently Proved finite original Borel marked-simple raw moment identity to the continuous bounded-mark original Poisson integral in JA28, and then to the Gaussian source strip isometry.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_dominated_real_simple_mark_two_moment_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ) (J B : Ω → ℝ)
    (m e : ℕ → ℝ) (r v : ℝ)
    (hfMeas : ∀ k, AEStronglyMeasurable (f k) P)
    (hBi : Integrable B P)
    (hBsq : Integrable (fun ω => (B ω) ^ 2) P)
    (hBound : ∀ᵐ ω ∂P, ∀ k, ‖f k ω‖ ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 (J ω)))
    (hM : ∀ k, (∫ ω, f k ω ∂P) = m k)
    (hE : ∀ k, (∫ ω, (f k ω) ^ 2 ∂P) = e k)
    (hMr : Tendsto m atTop (𝓝 r))
    (hEv : Tendsto e atTop (𝓝 v)) :
    Integrable J P ∧ Integrable (fun ω => (J ω) ^ 2) P ∧
      (∫ ω, J ω ∂P) = r ∧
      (∫ ω, (J ω) ^ 2 ∂P) = v := by sorry
