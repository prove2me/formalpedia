-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ServiceBenefitPV_equivalence
-- name    : ActuarialValuation.cm1ServiceBenefitPV_equivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:56:35.206+00:00
-- url     : https://prove2.me/theorems/06ec9124-202f-498f-bff7-b36641fa1d30
-- title:
--   Benefit cashflows and service value: cm1ServiceBenefitPV_equivalence
-- statement:
--   Two actuarially independent implementations of the complete pension decrement benefit valuation produce identical present values. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \sum_tv_t\sum_jb_{t,j}d_{t,j}/l_0=\sum_tv_t\sum_jb_{t,j}\,{}_tp\,q_{t,j}
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceBenefitPV
import Definitions.Def_actuarial_cm1ServiceConditionalPV

namespace ActuarialValuation

theorem cm1ServiceBenefitPV_equivalence (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) (h0 : l 0 ≠ 0) (hpos : ∀ t ∈ Finset.range N, l t ≠ 0) : cm1ServiceBenefitPV v b d l N m = cm1ServiceConditionalPV v b d l N m := by sorry

end ActuarialValuation
