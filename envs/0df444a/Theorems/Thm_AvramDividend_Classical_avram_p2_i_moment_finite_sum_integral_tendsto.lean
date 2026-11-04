-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_finite_sum_integral_tendsto
-- name    : AvramDividend.Classical.avram_p2_i_moment_finite_sum_integral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:18:35.329902+00:00
-- url     : https://prove2.me/theorems/dc55167d-74b9-4a46-9a6e-3115b7352e97
-- title:
--   Convergence of finite polynomial integrals from monomial moment convergence
-- statement:
--   For any filter-indexed family of measures on the real line and a limit measure, integrability of finitely many monomials and convergence of their real integrals imply convergence of the integrals of every fixed finite linear combination. This is a general filter finite-polynomial moment bridge, with no assumption of compact support on the approximating measures or of the desired continuous-test conclusion.

import Mathlib
open MeasureTheory Filter Topology
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_i_moment_finite_sum_integral_tendsto
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (s : Finset ℕ) (a : ℕ → ℝ)
    (hi : ∀ i k, k ∈ s → Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k ∈ s, Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : ∀ k ∈ s,
      Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
        (nhds (∫ z : ℝ, z ^ k ∂μ))) :
    Tendsto (fun i => ∫ z : ℝ, (∑ k ∈ s, a k * z ^ k) ∂μi i) l
      (nhds (∫ z : ℝ, (∑ k ∈ s, a k * z ^ k) ∂μ)) := by sorry
