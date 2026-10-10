-- Prove2me | Theorems.Thm_ActuarialValuation_panjerRecurrenceLaw_zero
-- name    : ActuarialValuation.panjerRecurrenceLaw_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:38:57.992983+00:00
-- url     : https://prove2.me/theorems/6a14cb86-1fdb-44c3-9671-02f4ef8d87a2
-- title:
--   Compound Poisson Panjer recurrence: panjerRecurrenceLaw_zero
-- statement:
--   A recurrence-law solution starts with exactly the Poisson zero-claims probability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_0=e^{-\lambda}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecurrenceLaw
import Definitions.Def_actuarial_panjerPoissonZero

namespace ActuarialValuation

theorem panjerRecurrenceLaw_zero (lambda : ℝ) (f g : ℕ → ℝ) (h : panjerRecurrenceLaw lambda f g) : g 0 = panjerPoissonZero lambda := by sorry

end ActuarialValuation
