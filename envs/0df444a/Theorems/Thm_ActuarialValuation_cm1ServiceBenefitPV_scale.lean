-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ServiceBenefitPV_scale
-- name    : ActuarialValuation.cm1ServiceBenefitPV_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:56:13.165558+00:00
-- url     : https://prove2.me/theorems/c08bf333-26d6-4ffe-8dbd-777571b530b8
-- title:
--   Benefit cashflows and service value: cm1ServiceBenefitPV_scale
-- statement:
--   Valuation is linear in the insured decrement benefit amounts. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V(cb)=cV(b)
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceBenefitPV

namespace ActuarialValuation

theorem cm1ServiceBenefitPV_scale (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) (c : ℝ) : cm1ServiceBenefitPV v (fun t j => c * b t j) d l N m = c * cm1ServiceBenefitPV v b d l N m := by sorry

end ActuarialValuation
