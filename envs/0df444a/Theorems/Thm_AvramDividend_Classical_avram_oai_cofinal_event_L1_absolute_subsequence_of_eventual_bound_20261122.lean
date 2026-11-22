-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_cofinal_event_L1_absolute_subsequence_of_eventual_bound_20261122
-- name    : AvramDividend.Classical.avram_oai_cofinal_event_L1_absolute_subsequence_of_eventual_bound_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:10:59.055043+00:00
-- url     : https://prove2.me/theorems/cd1d3912-5598-4d5e-bed5-131527619405
-- title:
--   L1-eventual global absolute error bounds yield a subsequence integrable at every index with restricted-event L1 error converging to zero
-- statement:
--   Given a genuine real-valued stochastic mesh error B_m with all sufficiently fine meshes integrable and global E|B_m|≤ε for every ε>0, extract an actual index selector r_j and prove all selected B_{r_j} are integrable, and for every event A the restricted absolute L1 error ∫_A|B_{r_j}| tends to zero. The selector may be nonmonotone; each index is selected using ε=1/(j+1) and eventual integrability. The pinned Mathlib one/(n+1) limit and squeeze establish global L1 convergence, and the previously remotely PROVED original Avram gaussian abs L1 global-to-restricted lemma eb24c6d7 gives every-event restricted convergence. This is the missing functional-analytic diagonalization needed to consume original allactivity positive stopping clock full dividend cash last-mesh error theorem and combine it with the true Gaussian plus compensated-jump Itô source. All proof obligations are genuine; no synthetic martingales or assumptions of convergence beyond the stated epsilon bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_abs_L1_global_to_restricted
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_cofinal_event_L1_absolute_subsequence_of_eventual_bound_20261122
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℕ → Ω → ℝ)
    (hSmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        Integrable (B m) P ∧
          (∫ ω, |B m ω| ∂P) ≤ ε) :
    ∃ r : ℕ → ℕ,
      (∀ j, Integrable (B (r j)) P) ∧
      (∀ A : Set Ω,
        (∀ j, Integrable (fun ω => |B (r j) ω|) (P.restrict A)) ∧
        Tendsto (fun j => ∫ ω in A, |B (r j) ω| ∂P)
          atTop (𝓝 (0 : ℝ))) := by sorry
