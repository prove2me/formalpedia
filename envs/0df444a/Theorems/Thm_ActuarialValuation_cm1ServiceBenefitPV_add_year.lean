-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ServiceBenefitPV_add_year
-- name    : ActuarialValuation.cm1ServiceBenefitPV_add_year
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:55:13.771897+00:00
-- url     : https://prove2.me/theorems/29119bf5-6bf0-4e7b-b17b-2914428b6334
-- title:
--   Benefit cashflows and service value: cm1ServiceBenefitPV_add_year
-- statement:
--   One more service-table year adds precisely its own discounted competing decrement benefits. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V_{N+1}=V_N+\sum_jv_Nb_{N,j}P_{N,j}
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceCohortCause
import Definitions.Def_actuarial_cm1ServiceBenefitPV

namespace ActuarialValuation

theorem cm1ServiceBenefitPV_add_year (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) : cm1ServiceBenefitPV v b d l (N+1) m = cm1ServiceBenefitPV v b d l N m + (∑ j ∈ Finset.range m, v N * b N j * cm1ServiceCohortCause l d N j) := by sorry

end ActuarialValuation
