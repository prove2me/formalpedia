-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ServiceConditionalPartition
-- name    : ActuarialValuation.cm1ServiceConditionalPartition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:53:25.811225+00:00
-- url     : https://prove2.me/theorems/b707032b-9217-4ffe-9e60-a56641db07df
-- title:
--   Cause probabilities and transitions: cm1ServiceConditionalPartition
-- statement:
--   Conditional probabilities partition next-year active survival from all competing exit causes. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p_t+\sum_jq_{t,j}=1
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceValid
import Definitions.Def_actuarial_cm1ServiceConditionalCause
import Definitions.Def_actuarial_cm1ServiceOneYearSurvival

namespace ActuarialValuation

theorem cm1ServiceConditionalPartition (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (N m t : ℕ) (hv : cm1ServiceValid l d N m) (ht : t < N) (hl : l t ≠ 0) : cm1ServiceOneYearSurvival l t + (∑ j ∈ Finset.range m, cm1ServiceConditionalCause l d t j) = 1 := by sorry

end ActuarialValuation
