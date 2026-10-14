-- Prove2me | Theorems.Thm_ActuarialValuation_ruRuinProb_certain
-- name    : ActuarialValuation.ruRuinProb_certain
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:47.415966+00:00
-- url     : https://prove2.me/theorems/216ff566-5540-443b-9daa-2065b67d4725
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruRuinProb_certain
-- statement:
--   All paths ruined implies unit ruin probability under a normalised finite probability model.
--
--   Mathematical relation:
--
--   $$
--   ruRuinProb\_certain
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinProbability

namespace ActuarialValuation

theorem ruRuinProb_certain {m : ℕ} (p : Fin m → ℝ) (hn : (∑ ω : Fin m, p ω)=1) : ruRuinProbability p (fun _ => True) = 1 := by sorry

end ActuarialValuation
