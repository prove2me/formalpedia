-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ForceBenefitPV_nonneg
-- name    : ActuarialValuation.cm1ForceBenefitPV_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:57:48.00199+00:00
-- url     : https://prove2.me/theorems/d16c3ae5-d3a5-447e-9fac-fb9508df54a6
-- title:
--   Valuation of continuous benefits: cm1ForceBenefitPV_nonneg
-- statement:
--   Valid mortality, benefit amount and term length yield nonnegative expected benefit PV. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \delta+\mu>0,\ \mu,B,T\ge0\Rightarrow PV_B\ge0
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2020), Policy Values, Chapter 7, printed page 250, Thiele's differential equation. Encyclopedia of Mathematics, Thiele differential equation, https://encyclopediaofmath.org/wiki/Thiele_differential_equation; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2020), Policy values and Thiele, https://www.kriso.ee/actuarial-mathematics-life-contingent-risks-3rd-db-9781108478083.html; Oxford Mathematics actuarial reserves and Thiele lecture, https://www.stats.ox.ac.uk/~winkel/bs4b11.pdf. Parent topic: Continuous force of interest and mortality, constant-force prospective reserves, Thiele's differential equation and terminal condition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Additional IFoA source syllabus: https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1ForceBenefitPV

namespace ActuarialValuation

theorem cm1ForceBenefitPV_nonneg (δ μ B T : ℝ) (hk : 0 < δ+μ) (hT : 0 ≤ T) (hμ : 0 ≤ μ) (hB : 0 ≤ B) : 0 ≤ cm1ForceBenefitPV δ μ B T := by sorry

end ActuarialValuation
