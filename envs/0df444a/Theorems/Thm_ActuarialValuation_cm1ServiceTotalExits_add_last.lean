-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ServiceTotalExits_add_last
-- name    : ActuarialValuation.cm1ServiceTotalExits_add_last
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:49:53.081853+00:00
-- url     : https://prove2.me/theorems/8cde0314-3c8b-419a-a808-55c659f429be
-- title:
--   Pension cohort accounting: cm1ServiceTotalExits_add_last
-- statement:
--   Appending one cohort year adds its own multi-cause exits. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_{0:N+1}=D_{0:N}+D_N
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceAnnualExit
import Definitions.Def_actuarial_cm1ServiceTotalExits

namespace ActuarialValuation

theorem cm1ServiceTotalExits_add_last (d : ℕ → ℕ → ℝ) (N m : ℕ) : cm1ServiceTotalExits d (N+1) m = cm1ServiceTotalExits d N m + cm1ServiceAnnualExit d N m := by sorry

end ActuarialValuation
