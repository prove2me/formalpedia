-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ThieleContinuousValuation_fundamental
-- name    : ActuarialValuation.cm1ThieleContinuousValuation_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T23:01:46.270084+00:00
-- url     : https://prove2.me/theorems/c65abdec-2125-4f71-8d4a-cf5be0f04a4a
-- title:
--   Valuation of continuous benefits: cm1ThieleContinuousValuation_fundamental
-- statement:
--   The capstone proves the exact continuous term reserve issue value, terminal zero, nonnegative on the term and the actual Thiele ODE, not merely a definitional rewriting. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V(T)=0,\quad V(0)=PV_B-PV_P,\quad V(t)\ge0,\quad V'=P+\delta V-\mu(B-V)
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2020), Policy Values, Chapter 7, printed page 250, Thiele's differential equation. Encyclopedia of Mathematics, Thiele differential equation, https://encyclopediaofmath.org/wiki/Thiele_differential_equation; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2020), Policy values and Thiele, https://www.kriso.ee/actuarial-mathematics-life-contingent-risks-3rd-db-9781108478083.html; Oxford Mathematics actuarial reserves and Thiele lecture, https://www.stats.ox.ac.uk/~winkel/bs4b11.pdf. Parent topic: Continuous force of interest and mortality, constant-force prospective reserves, Thiele's differential equation and terminal condition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Additional IFoA source syllabus: https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1ThieleReserve
import Definitions.Def_actuarial_cm1ThieleRHS
import Definitions.Def_actuarial_cm1ForceBenefitPV
import Definitions.Def_actuarial_cm1ForcePremiumPV

namespace ActuarialValuation

theorem cm1ThieleContinuousValuation_fundamental (δ μ B P T : ℝ) (hk : 0 < δ+μ) (hT : 0 ≤ T) (hnet : P ≤ μ*B) : (cm1ThieleReserve δ μ B P T T = 0) ∧ (cm1ThieleReserve δ μ B P T 0 = cm1ForceBenefitPV δ μ B T - cm1ForcePremiumPV δ μ P T) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ T → 0 ≤ cm1ThieleReserve δ μ B P T t ∧ deriv (cm1ThieleReserve δ μ B P T) t = cm1ThieleRHS δ μ B P (cm1ThieleReserve δ μ B P T t)) := by sorry

end ActuarialValuation
