-- Prove2me | Theorems.Thm_ActuarialValuation_cm1EffectiveDiscount_identity
-- name    : ActuarialValuation.cm1EffectiveDiscount_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:49:35.956014+00:00
-- url     : https://prove2.me/theorems/722446d4-fda6-4496-99c3-29400cee0949
-- title:
--   Interest rate algebra: cm1EffectiveDiscount_identity
-- statement:
--   Interest and effective discount rates satisfy the exact single-year relationship. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (1+i)d=i
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 2. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1EffectiveDiscount

namespace ActuarialValuation

theorem cm1EffectiveDiscount_identity (i : ℝ) (hi : -1 < i) : (1+i) * cm1EffectiveDiscount i = i := by sorry

end ActuarialValuation
