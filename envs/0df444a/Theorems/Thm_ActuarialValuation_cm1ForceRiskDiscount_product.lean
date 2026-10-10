-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ForceRiskDiscount_product
-- name    : ActuarialValuation.cm1ForceRiskDiscount_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:51:48.952409+00:00
-- url     : https://prove2.me/theorems/cead441b-3e8e-42ab-8e59-f1f584697c89
-- title:
--   Continuous survival and discount: cm1ForceRiskDiscount_product
-- statement:
--   Combined survival-contingent discount is the product of mortality and interest factors. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e^{-(\delta+\mu)t}=e^{-\delta t}e^{-\mu t}
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2020), Policy Values, Chapter 7, printed page 250, Thiele's differential equation. Encyclopedia of Mathematics, Thiele differential equation, https://encyclopediaofmath.org/wiki/Thiele_differential_equation; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2020), Policy values and Thiele, https://www.kriso.ee/actuarial-mathematics-life-contingent-risks-3rd-db-9781108478083.html; Oxford Mathematics actuarial reserves and Thiele lecture, https://www.stats.ox.ac.uk/~winkel/bs4b11.pdf. Parent topic: Continuous force of interest and mortality, constant-force prospective reserves, Thiele's differential equation and terminal condition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Additional IFoA source syllabus: https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1ForceSurvival
import Definitions.Def_actuarial_cm1ForceDiscount
import Definitions.Def_actuarial_cm1ForceRiskDiscount

namespace ActuarialValuation

theorem cm1ForceRiskDiscount_product (δ μ t : ℝ) : cm1ForceRiskDiscount δ μ t = cm1ForceDiscount δ t * cm1ForceSurvival μ t := by sorry

end ActuarialValuation
