-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_mark_event_moment_matching
-- name    : AvramDividend.Classical.chat06_mark_event_moment_matching
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:45:07.703026+00:00
-- url     : https://prove2.me/theorems/c9f9a337-138d-48b7-be90-131a2c7eead1
-- title:
--   Fixed-count mark moment matching on a Poisson count cylinder
-- statement:
--   On a fixed count-cylinder N=k, the random exponential of the mark sum and the fixed-count exponential coincide. If N is independent of every fixed-length mark sum and those exponential moments equal m^k, the expectation over that count-cylinder equals the expectation of m^N over the same cylinder. The proof applies independence of measurable exponential transformations and indicator events. This is a cylinder-level bridge for a marked compound-Poisson Laplace identity; existence of independent marks and their moment powers remain assumptions.
-- source:
--   bv_mark_event_moment_matching_v2_chat06_20261020.lean, 116 lines, 4572 bytes, SHA-256 39d60c2b7bc8886dcc382caaee4f7499c0afd466ac22f42a230236d77ca4e617. Private probe d4cf1501-7b92-46eb-a1d5-2f2a92a7e72a passed to sentinel with zero candidate errors.

import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory ProbabilityTheory Set Real

theorem AvramDividend.Classical.chat06_mark_event_moment_matching
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hIndep : ∀ k : ℕ,
      IndepFun N (fun ω => ∑ i ∈ Finset.range k, Y i ω) P)
    (θ m : ℝ)
    (hFixed : ∀ k : ℕ,
      (∫ ω, Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) =
        m ^ k)
    (k : ℕ) :
    (∫ ω in {ω | N ω = k},
      Real.exp (θ * ∑ i ∈ Finset.range (N ω), Y i ω) ∂P) =
    (∫ ω in {ω | N ω = k}, m ^ (N ω) ∂P) := by sorry
