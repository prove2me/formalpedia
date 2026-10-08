-- Prove2me | Theorems.Thm_AvramDividend_Classical_bounded_stopping_dyadic_grid_approximation
-- name    : AvramDividend.Classical.bounded_stopping_dyadic_grid_approximation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:34:57.061216+00:00
-- url     : https://prove2.me/theorems/68cdb033-cbf7-4640-a303-5d06c3c7a761
-- title:
--   Bounded stopping times admit upper dyadic finite-grid approximations
-- statement:
--   A nonnegative bounded stopping time τ in the original continuous-time filtration can be approximated from above by finite-valued dyadic-grid random times τn. Each τn is supported on a finite grid and every event {τn=s} is measurable at its grid time s, because the stopping-time hypothesis supplies events {τ≤s} in F_s and the filtration is increasing. The grid approximations dominate τ and converge pointwise to τ. A constructive proof rounds τ upward to a mesh of size 2^{-n} and restricts the possible grid points to the finite interval [0,T+mesh]. This is the exact measurable finite-grid approximation needed to deduce bounded stopping Lévy increment transforms from the published finite-grid theorem.
-- source:
--   Standard dyadic proof of the strong Markov property for càdlàg Lévy processes; Mathlib.Probability.Process.Stopping IsStoppingTime, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474; Avram et al (2007), Proposition 1.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bounded_stopping_dyadic_grid_approximation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    ∃ (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0),
      (∀ n ω, τn n ω ∈ grid n) ∧
      (∀ n s, s ∈ grid n →
        MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
      (∀ ω n, τ ω ≤ τn n ω) ∧
      (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) := by sorry
