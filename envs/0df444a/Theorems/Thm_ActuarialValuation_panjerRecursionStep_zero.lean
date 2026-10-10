-- Prove2me | Theorems.Thm_ActuarialValuation_panjerRecursionStep_zero
-- name    : ActuarialValuation.panjerRecursionStep_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:37:41.820072+00:00
-- url     : https://prove2.me/theorems/c68fe3ae-538e-46d0-83d6-241990279b57
-- title:
--   Compound Poisson Panjer recurrence: panjerRecursionStep_zero
-- statement:
--   First nonzero aggregate-loss coefficient depends only on a single size-one claim. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_1=\lambda f_1g_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecursionStep

namespace ActuarialValuation

theorem panjerRecursionStep_zero (lambda : ℝ) (f g : ℕ → ℝ) : panjerRecursionStep lambda f g 0 = lambda * f 1 * g 0 := by sorry

end ActuarialValuation
