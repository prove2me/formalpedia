-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_nonpositive_exponential_expectation_dct
-- name    : AvramDividend.Classical.avram_a77_nonpositive_exponential_expectation_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:16:29.311639+00:00
-- url     : https://prove2.me/theorems/ca9d2db2-4a2e-4971-a4c0-cfa460d2a1d6
-- title:
--   Bounded exponential expectation converges for pointwise a.e. limits of nonpositive source mark exponents
-- statement:
--   Given measurable real exponent functions f_n on one probability space which are nonpositive almost everywhere simultaneously and converge almost everywhere to an exponent J, the expectations of exp(f_n) converge to E exp(J). The unit bound 0<exp(f_n)<=1 and integrability of 1 give the real dominated convergence theorem. This is exactly the stochastic dominated convergence step for the original Avram a77 physical marked negative jump Laplace limit once its finite Borel simple exponential coefficients have been constructed. No independence assumption or auxiliary probability space.
-- source:
--   Avram mission 1300fbe7, source 5b48325d 8bb full physical marked jump Laplace finite-simple-to-full limit. Pinned Mathlib MeasureTheory.tendsto_integral_of_dominated_convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_a77_nonpositive_exponential_expectation_dct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (J : Ω → ℝ)
    (hMeas : ∀ n, Measurable (f n))
    (hLimit : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (J ω)))
    (hNonpos : ∀ᵐ ω ∂P, ∀ n, f n ω ≤ 0) :
    Tendsto (fun n => ∫ ω, Real.exp (f n ω) ∂P)
      atTop (𝓝 (∫ ω, Real.exp (J ω) ∂P)) := by sorry
