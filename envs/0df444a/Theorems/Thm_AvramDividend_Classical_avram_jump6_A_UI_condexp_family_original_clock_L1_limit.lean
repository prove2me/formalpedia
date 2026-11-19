-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_UI_condexp_family_original_clock_L1_limit
-- name    : AvramDividend.Classical.avram_jump6_A_UI_condexp_family_original_clock_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:28:17.415706+00:00
-- url     : https://prove2.me/theorems/e50772dd-f472-400c-bbe7-5ad90408cdfe
-- title:
--   Original physical upper-clock conditional samples admit an L1 limit by uniform integrability
-- statement:
--   For any integrable terminal random variable, conditional samples along arbitrary sub-sigma-algebras form a uniformly integrable sequence. If they converge pointwise almost everywhere to the actual stopped physical source, that source is integrable and the convergence is in L1. This is the exact UI step needed to replace an unnecessary Gaussian second-moment assumption in bounded-stop optional sampling.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_UI_condexp_family_original_clock_L1_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hg : Integrable g P)
    (f : ℕ → Ω → ℝ) (ℋ : ℕ → MeasurableSpace Ω)
    (hℋ : ∀ n, ℋ n ≤ mΩ)
    (hCE : ∀ n, f n =ᵐ[P] condExp (ℋ n) P g)
    (M : Ω → ℝ)
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => f n ω) atTop (nhds (M ω))) :
    Integrable M P ∧
      Tendsto (fun n => eLpNorm (fun ω => f n ω - M ω) 1 P)
        atTop (nhds 0) := by sorry
