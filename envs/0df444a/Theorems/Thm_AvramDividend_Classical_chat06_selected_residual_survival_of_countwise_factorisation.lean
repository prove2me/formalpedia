-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_selected_residual_survival_of_countwise_factorisation
-- name    : AvramDividend.Classical.chat06_selected_residual_survival_of_countwise_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:09:27.942851+00:00
-- url     : https://prove2.me/theorems/1876d93e-7a03-4e31-bc0b-c81c0bda7540
-- title:
--   Gluing countwise conditional residual survival over a random index
-- statement:
--   For a measurable integer-valued count N, and a family of measurable residual waiting times F(n), suppose survival at a fixed threshold factors with the same scalar c on every event N=n. The randomly selected waiting time F(N) then has unconditional survival probability c. The result rigorously sums the countably many disjoint count events and supports the transition from fixed-count exponential residual memorylessness to a randomly indexed residual survival identity. Its countwise factorisation premise must still be proved from arrival cylinders for the concrete Poisson process.
-- source:
--   Source bv_selected_residual_survival_countwise_gluing_v2_chat06_20261021.lean, 81 lines; exact SHA-256 f1eb7f9492f2baaaf77e714870ad5b1871b1425fe777685997c8da539bb5d76f; private probe d922f3c3-ec8e-46ef-aad9-a0263abb170b passed source elaboration to sentinel with zero candidate errors at pinned revision; official target proof not yet submitted.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_selected_residual_survival_of_countwise_factorisation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (u : ℝ) (c : ℝ≥0∞)
    (hFactor : ∀ n : ℕ,
      P {ω | N ω = n ∧ u < F n ω} =
        P {ω | N ω = n} * c) :
    P {ω | u < F (N ω) ω} = c := by sorry
