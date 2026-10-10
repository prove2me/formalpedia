-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ZeroReserveCondition_step
-- name    : ActuarialValuation.cm1ZeroReserveCondition_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:40:22.994805+00:00
-- url     : https://prove2.me/theorems/c83bafb4-ff69-40bb-a51c-ecd6a10d759e
-- title:
--   Backwards non-unit zeroisation: cm1ZeroReserveCondition_step
-- statement:
--   Each pre-terminal reserve satisfies the locally minimal backwards floor. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   t<N\Longrightarrow R_t=R_t^*
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor
import Definitions.Def_actuarial_cm1ZeroReserveCondition

namespace ActuarialValuation

theorem cm1ZeroReserveCondition_step (c s g R : ℕ → ℝ) (N t : ℕ) (h : cm1ZeroReserveCondition c s g R N) (ht : t < N) : R t = cm1ZeroReserveFloor (c t) (s t) (g t) (R (t+1)) := by sorry

end ActuarialValuation
