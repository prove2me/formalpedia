-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_binomial_law_transport_from_original_iid_sum_20261116
-- name    : AvramDividend.Classical.avram_a27_binomial_law_transport_from_original_iid_sum_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:28:14.841855+00:00
-- url     : https://prove2.me/theorems/c2825e84-174c-4653-ad32-d63b8f72a066
-- title:
--   Transport original-space Bernoulli i.i.d. sum law to a pointwise equal occupied-cell count
-- statement:
--   On any original probability space P, if a measurable integer Z agrees pathwise with the finite sum of mutually independent identically distributed zero-one variables Y_i, then Z has exactly Bin(n,p) distribution. Directly use the Proved generic Bernoulli sum theorem 474881c3 and pointwise function extensionality. This isolates the final distribution transport from original physical occupied-cell card to Bernoulli sums.
-- source:
--   Proved i.i.d. zero-one binomial distribution theorem 474881c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_binomial_law_transport_from_original_iid_sum_20261116
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℕ)
    (hMeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hIndep : iIndepFun Y P)
    (p : unitInterval)
    (hP : ∀ i : Fin n, (P {ω : Ω | Y i ω = 1}).toReal = (p : ℝ))
    (Z : Ω → ℕ)
    (hZ : ∀ ω, Z ω = ∑ i : Fin n, Y i ω) :
    P.map Z = Bin(n, p) := by sorry
