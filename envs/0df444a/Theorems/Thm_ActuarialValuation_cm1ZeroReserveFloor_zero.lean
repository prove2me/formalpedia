-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ZeroReserveFloor_zero
-- name    : ActuarialValuation.cm1ZeroReserveFloor_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:01:07.4598+00:00
-- url     : https://prove2.me/theorems/f272ec6b-66fe-46b0-9d7b-21a94933efb1
-- title:
--   Backwards non-unit zeroisation: cm1ZeroReserveFloor_zero
-- statement:
--   If projected cashflow already covers the future reserve need, zero opening reserve suffices. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c\ge sR_{\rm next}\Longrightarrow R_t^*=0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor

namespace ActuarialValuation

theorem cm1ZeroReserveFloor_zero (c s g R : ℝ) (hg : 0 < g) (h : s*R ≤ c) : cm1ZeroReserveFloor c s g R = 0 := by sorry

end ActuarialValuation
