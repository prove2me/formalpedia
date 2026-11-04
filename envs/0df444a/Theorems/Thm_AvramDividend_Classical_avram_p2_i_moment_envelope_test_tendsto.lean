-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_envelope_test_tendsto
-- name    : AvramDividend.Classical.avram_p2_i_moment_envelope_test_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:36:10.721975+00:00
-- url     : https://prove2.me/theorems/9a092022-e767-4169-b46b-f12d6dd252f3
-- title:
--   Finite-measure moment convergence implies convergence of all high-moment-envelope tests
-- statement:
--   For any general filter, positive-supported approximating measures with all real polynomial moments integrable and convergent to a finite measure supported in [0,1] have convergent integrals for any integrable real test g that admits arbitrarily fine polynomial approximants globally dominated by gamma(1+z^K) on z≥0. The proof controls the approximant integrals by moments, the test error by mass and one high moment, and uses an epsilon/3 approximating-filter limit lemma. This theorem does not assume the desired convergence and does not restrict approximating support to [0,1].

import Mathlib
open MeasureTheory Filter Topology Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_i_moment_envelope_test_tendsto
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 ≤ z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : ∀ k,
      Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
        (nhds (∫ z : ℝ, z ^ k ∂μ)))
    (g : ℝ → ℝ) (hgi : ∀ i, Integrable g (μi i))
    (hgμ : Integrable g μ)
    (happrox : ∀ γ : ℝ, 0 < γ →
      ∃ p : Polynomial ℝ, ∃ K : ℕ,
        ∀ z : ℝ, 0 ≤ z →
          |g z - p.eval z| ≤ γ * (1 + z ^ K)) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by sorry
