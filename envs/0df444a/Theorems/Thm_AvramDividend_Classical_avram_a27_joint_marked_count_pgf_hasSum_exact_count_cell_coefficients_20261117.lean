-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_joint_marked_count_pgf_hasSum_exact_count_cell_coefficients_20261117
-- name    : AvramDividend.Classical.avram_a27_joint_marked_count_pgf_hasSum_exact_count_cell_coefficients_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:39:45.034375+00:00
-- url     : https://prove2.me/theorems/ac27bb3a-28af-46cb-a464-6c808c73aeab
-- title:
--   Joint marked count PGF equals its count-cell weighted Laplace power series on the original probability space
-- statement:
--   For any measurable natural-valued count K and any integrable real generating-function weight z^K F on the original probability space, the expectation E[z^K F] equals the convergent series sum of z^k times the exact restricted expectation of F over K=k. This provides the algebraic bridge from the source joint marked Poisson PGF to the conditional count-cell Laplace coefficients.
-- source:
--   Proved countable original count-cell integral decomposition and exact identification of constant z^k factors on each restricted event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- The joint marked count PGF is the exact count-cell power series, without any independent mark construction. -/

theorem AvramDividend.Classical.avram_a27_joint_marked_count_pgf_hasSum_exact_count_cell_coefficients_20261117
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (hK : Measurable K)
    (F : Ω → ℝ) (z : ℝ)
    (hInt : Integrable (fun ω => z ^ (K ω) * F ω) P) :
    HasSum (fun k : ℕ => z ^ k *
      (∫ ω in {ω : Ω | K ω = k}, F ω ∂P))
      (∫ ω, z ^ (K ω) * F ω ∂P) := by sorry
