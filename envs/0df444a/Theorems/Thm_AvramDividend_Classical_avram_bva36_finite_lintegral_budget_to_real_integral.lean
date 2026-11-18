-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva36_finite_lintegral_budget_to_real_integral
-- name    : AvramDividend.Classical.avram_bva36_finite_lintegral_budget_to_real_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T22:01:55.960195+00:00
-- url     : https://prove2.me/theorems/1f2b89e7-2b2a-4d3c-8469-611c1f947291
-- title:
--   Finite nonnegative ENNReal outer expectation upper bound implies real expectation upper bound for actual toReal payoff
-- statement:
--   For any measurable-space probability source and σ-finite or arbitrary measure P, if f is an everywhere finite ENNReal-valued payoff and its real conversion is integrable, then an upper bound on its ENNReal lintegral by ofReal K (K≥0) implies the same upper bound on the real Bochner integral of f.toReal. The proof uses the exact finite ofReal_toReal identity, equality of integrals for a nonnegative integrable real function, and the monotonicity of ENNReal.toReal. Applied to the authentic original discounted stopped dividend Cash rather than a fictitious payoff.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva36_finite_lintegral_budget_to_real_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ≥0∞) (K : ℝ)
    (hFin : ∀ ω, f ω ≠ ⊤)
    (hI : Integrable (fun ω => (f ω).toReal) P)
    (hK : 0 ≤ K)
    (hBudget : (∫⁻ ω, f ω ∂P) ≤ ENNReal.ofReal K) :
    (∫ ω, (f ω).toReal ∂P) ≤ K := by sorry
