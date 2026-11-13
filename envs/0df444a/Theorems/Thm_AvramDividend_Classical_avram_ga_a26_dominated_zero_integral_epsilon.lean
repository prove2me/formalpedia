-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a26_dominated_zero_integral_epsilon
-- name    : AvramDividend.Classical.avram_ga_a26_dominated_zero_integral_epsilon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:01:37.71542+00:00
-- url     : https://prove2.me/theorems/6299971d-6897-46c3-a846-634472d83ca2
-- title:
--   Dominated zero limit gives eventual integral epsilon bound and integrability
-- statement:
--   An original-process sequence of measurable real residuals that has an integrable dominating envelope and tends to zero almost surely is integrable at each index and has integral eventually no greater than any positive epsilon. This isolates the dominated convergence step needed for a stopped terminal Gaussian cell.
-- source:
--   Dominated convergence corollary for Avram gledger179 terminal stopped Gaussian source L1.

import Mathlib
open MeasureTheory Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a26_dominated_zero_integral_epsilon
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable (f m) P)
    (hG : Integrable g P)
    (hDom : ∀ m, ∀ᵐ ω ∂P, ‖f m ω‖ ≤ g ω)
    (hLim : ∀ᵐ ω ∂P, Tendsto (fun m => f m ω) atTop (nhds (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (f m) P ∧ (∫ ω, f m ω ∂P) ≤ ε := by sorry
