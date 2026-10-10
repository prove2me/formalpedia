-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ServiceBenefitPV_add_benefits
-- name    : ActuarialValuation.cm1ServiceBenefitPV_add_benefits
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:56:02.009615+00:00
-- url     : https://prove2.me/theorems/21c558d0-83b5-444d-8842-e3a5907c8bbd
-- title:
--   Benefit cashflows and service value: cm1ServiceBenefitPV_add_benefits
-- statement:
--   Combining pension decrement benefits adds their monetary expected values exactly. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V(b+c)=V(b)+V(c)
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceBenefitPV

namespace ActuarialValuation

theorem cm1ServiceBenefitPV_add_benefits (v : ℕ → ℝ) (b c d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) : cm1ServiceBenefitPV v (fun t j => b t j + c t j) d l N m = cm1ServiceBenefitPV v b d l N m + cm1ServiceBenefitPV v c d l N m := by sorry

end ActuarialValuation
