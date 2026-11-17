-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_iid_zero_one_finite_sum_has_binomial_law_20261116
-- name    : AvramDividend.Classical.avram_a26_iid_zero_one_finite_sum_has_binomial_law_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:18:34.942203+00:00
-- url     : https://prove2.me/theorems/474881c3-4d0f-42e5-8030-6a7ec21d3394
-- title:
--   A finite family of independent identically distributed zero-one source counts has the binomial law
-- statement:
--   For a finite family of measurable natural-valued random variables taking values only 0 and 1 on the original probability space, mutually independent under P and with common probability p of value 1, their finite sum has exactly Bin(n,p) distribution. Prove from the pinned Mathlib independent random-variable product law and the binomial distribution's setBernoulli or finite binomial identity. This is an abstract same-measure combinatorial theorem used to identify the physical Lévy occupied-grid binomial law without introducing a companion source.
-- source:
--   Finite iid Bernoulli convolution / binomial theorem; pinned Mathlib ProbabilityTheory.iIndepFun, ProbabilityTheory.binomial.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_iid_zero_one_finite_sum_has_binomial_law_20261116
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℕ)
    (hMeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hIndep : iIndepFun Y P)
    (p : unitInterval)
    (hP : ∀ i : Fin n, (P {ω : Ω | Y i ω = 1}).toReal = (p : ℝ)) :
    P.map (fun ω : Ω => ∑ i : Fin n, Y i ω) = Bin(n, p) := by sorry
