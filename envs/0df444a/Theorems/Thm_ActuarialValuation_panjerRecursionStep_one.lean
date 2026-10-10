-- Prove2me | Theorems.Thm_ActuarialValuation_panjerRecursionStep_one
-- name    : ActuarialValuation.panjerRecursionStep_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:38:02.494088+00:00
-- url     : https://prove2.me/theorems/f60cf8e7-8b41-442b-b38e-965aded28278
-- title:
--   Compound Poisson Panjer recurrence: panjerRecursionStep_one
-- statement:
--   At aggregate loss two, distinguish two unit claims and one severity-two claim. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_2=\frac{\lambda}{2}(f_1g_1+2f_2g_0)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecursionStep

namespace ActuarialValuation

theorem panjerRecursionStep_one (lambda : ℝ) (f g : ℕ → ℝ) : panjerRecursionStep lambda f g 1 = lambda / 2 * (f 1 * g 1 + 2 * f 2 * g 0) := by sorry

end ActuarialValuation
