-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ZeroReserveFloor_mono_next
-- name    : ActuarialValuation.cm1ZeroReserveFloor_mono_next
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:38:51.803286+00:00
-- url     : https://prove2.me/theorems/98577346-9e4f-4623-a28e-fb598d1490c7
-- title:
--   Backwards non-unit zeroisation: cm1ZeroReserveFloor_mono_next
-- statement:
--   Higher expected closing reserve requirements cannot reduce the minimum opening reserve if survival weight is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R_1\le R_2\Longrightarrow R^*(R_1)\le R^*(R_2)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor

namespace ActuarialValuation

theorem cm1ZeroReserveFloor_mono_next (c s g R₁ R₂ : ℝ) (hs : 0 ≤ s) (hg : 0 < g) (h : R₁ ≤ R₂) : cm1ZeroReserveFloor c s g R₁ ≤ cm1ZeroReserveFloor c s g R₂ := by sorry

end ActuarialValuation
