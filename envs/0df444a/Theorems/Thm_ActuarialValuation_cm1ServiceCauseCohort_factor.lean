-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ServiceCauseCohort_factor
-- name    : ActuarialValuation.cm1ServiceCauseCohort_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:53:40.530734+00:00
-- url     : https://prove2.me/theorems/cc7e2d0a-b6b1-47c4-8294-62e8e64da393
-- title:
--   Cause probabilities and transitions: cm1ServiceCauseCohort_factor
-- statement:
--   The exact service-cohort survival times conditional decrement probability equals the unconditional cause exit mass. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   {}_tp\,q_{t,j}=d_{t,j}/l_0
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceSurvivalMass
import Definitions.Def_actuarial_cm1ServiceConditionalCause
import Definitions.Def_actuarial_cm1ServiceCohortCause

namespace ActuarialValuation

theorem cm1ServiceCauseCohort_factor (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (t j : ℕ) (h0 : l 0 ≠ 0) (ht : l t ≠ 0) : cm1ServiceSurvivalMass l t * cm1ServiceConditionalCause l d t j = cm1ServiceCohortCause l d t j := by sorry

end ActuarialValuation
