-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_independent_count_cell_mark_mean_ws01b
-- name    : AvramDividend.Classical.poisson_independent_count_cell_mark_mean_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:07:23.816226+00:00
-- url     : https://prove2.me/theorems/75e8ec36-a3d4-45ad-a454-f39389ed1f14
-- title:
--   True Poisson count-cell marked-sum mean from count–mark independence
-- statement:
--   For a measurable natural count and integrable identically-law marks, if the count is independent of the entire mark sequence, then on the event count=j the expectation of the first j marks equals P(count=j)·j·E(mark). A genuine restricted probability integral, one step towards Campbell's formula; no private point-process assumptions.
-- source:
--   Adapted to independent public Mathlib interfaces from LeanLevy PoissonPointFamily count-cell disintegration (MIT, 2026 LeanLevy Contributors); uses canonically proved finite mark mean theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_identically_law_fixed_marks_expectation_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.poisson_independent_count_cell_mark_mean_ws01b
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (j : ℕ) (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) :
    (∫ ω in {ω | K ω = j},
      ∑ n ∈ Finset.range j, f (Y n ω) ∂μ) =
      μ.real {ω | K ω = j} *
        ((j : ℝ) * ∫ y, f y ∂ν) := by sorry
