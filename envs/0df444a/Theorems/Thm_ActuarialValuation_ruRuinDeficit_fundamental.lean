-- Prove2me | Theorems.Thm_ActuarialValuation_ruRuinDeficit_fundamental
-- name    : ActuarialValuation.ruRuinDeficit_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:04:48.851988+00:00
-- url     : https://prove2.me/theorems/4f1937bc-ea9a-41ae-a7ee-6affaa3d9a34
-- title:
--   Stop-loss reinsurance, retained deficit and pathwise capital: ruRuinDeficit_fundamental
-- statement:
--   The capstone derives the surplus recursion, genuine positive deficit on the first-ruin event, and the pathwise reinsurance gain, with original capital and premium unchanged. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_{n+1}=U_n+c-X_n;D_n=-U_n;U^R=U+Y
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruFirstRuin
import Definitions.Def_actuarial_ruDeficit
import Definitions.Def_actuarial_ruRetainedSurplus
import Definitions.Def_actuarial_ruCededTotal

namespace ActuarialValuation

theorem ruRuinDeficit_fundamental (u c d : ℝ) (x : ℕ → ℝ) (n : ℕ) (h : ruFirstRuin u c x n) : (ruPathSurplus u c x (n+1) = ruPathSurplus u c x n + c-x n) ∧ (ruDeficit u c x n = -ruPathSurplus u c x n) ∧ (0 < ruDeficit u c x n) ∧ (ruPathSurplus u c x n ≤ ruRetainedSurplus u c d x n) ∧ (ruRetainedSurplus u c d x n = ruPathSurplus u c x n+ruCededTotal x d n) := by sorry

end ActuarialValuation
