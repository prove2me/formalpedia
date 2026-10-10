-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ServiceTerminalMass_nonneg
-- name    : ActuarialValuation.cm1ServiceTerminalMass_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:53:54.801482+00:00
-- url     : https://prove2.me/theorems/9b896fae-f5f4-4082-a6f9-a371f44fbc60
-- title:
--   Cause probabilities and transitions: cm1ServiceTerminalMass_nonneg
-- statement:
--   The probability of staying in service through retirement valuation horizon is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   l_N/l_0\ge0
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Multiple State Models, Chapter 8, printed page 256, multiple decrement models; Chapter 9, page 297, pension service tables. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapters 8-9, multiple decrement models and pension service tables, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: Pension service tables, retirement withdrawal and death as competing decrement causes, conservation of cohort mass and actuarial benefit PV. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceTerminalMass

namespace ActuarialValuation

theorem cm1ServiceTerminalMass_nonneg (l : ℕ → ℝ) (N : ℕ) (h0 : 0 < l 0) (hN : 0 ≤ l N) : 0 ≤ cm1ServiceTerminalMass l N := by sorry

end ActuarialValuation
