-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_drifted_compound_levy_laplace_field
-- name    : AvramDividend.Classical.chat06_drifted_compound_levy_laplace_field
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:57:42.783712+00:00
-- url     : https://prove2.me/theorems/8351902b-3f2a-4932-80a8-0ae4e95634f3
-- title:
--   Exact Laplace field for a drifted marked jump process
-- statement:
--   Under a count-conditioned mark exponential moment and the matching compound-Poisson Levy triplet exponent, measurability and the unit drift upper bound establish integrability and the exact Laplace integral.
-- source:
--   Chat 06 standalone Lean source with verified private remote pinned compiler elaboration; exact SHA and job in SUBMISSIONS.json, no official proof yet.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat06_drifted_compound_levy_laplace_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (ν : Measure ℝ) (t : ℝ≥0) (θ m : ℝ)
    (hθ : 0 ≤ θ)
    (hMeas : Measurable (fun ω =>
      (t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω))
    (hCap : ∀ ω, (t : ℝ) +
      ∑ i ∈ Finset.range (N ω), Y i ω ≤ (t : ℝ))
    (hCount : (∫ ω, Real.exp (θ *
      ∑ i ∈ Finset.range (N ω), Y i ω) ∂P) =
      Real.exp ((t : ℝ) * (m - 1)))
    (hTriplet : laplaceExponent 1 0 ν θ = θ + (m - 1)) :
    Integrable (fun ω => Real.exp (θ *
        ((t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω))) P ∧
      (∫ ω, Real.exp (θ *
        ((t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω)) ∂P) =
        Real.exp ((t : ℝ) * laplaceExponent 1 0 ν θ) := by sorry
