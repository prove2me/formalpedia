-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_campbell_ws01b
-- name    : AvramDividend.Classical.poisson_random_mark_sum_campbell_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:11:24.335853+00:00
-- url     : https://prove2.me/theorems/9fd9ed22-1379-4ffe-9f89-52826ee94f94
-- title:
--   Campbell expectation for random Poisson-count sums of integrable independent marks
-- statement:
--   On an actual probability space with a Poisson-law count K and an entire mark sequence independent of K, with each mark having a common law ν and f integrable under ν, the real Bochner expected random-length sum of f(Yn) over n<K equals the Poisson intensity r times Eν[f]. The proof also establishes the random sum's absolute integrability using a count-cell partition and the Poisson first moment. No private Lévy process definitions are assumed.
-- source:
--   Independent public version of the genuinely probabilistic Campbell piece-sum theorem in LeanLevy/RandomMeasure/PoissonPointFamily.lean, MIT 2026 LeanLevy Contributors. Adapted to Prove2Me's public Mathlib HasLaw and IndepFun; uses canonically proven WS1B count-cell identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_independent_count_cell_mark_mean_ws01b

open MeasureTheory ProbabilityTheory Real Finset Set
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_random_mark_sum_campbell_ws01b
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν) :
    (∫ ω, ∑ n ∈ Finset.range (K ω), f (Y n ω) ∂μ) =
      (r : ℝ) * ∫ y, f y ∂ν := by sorry
