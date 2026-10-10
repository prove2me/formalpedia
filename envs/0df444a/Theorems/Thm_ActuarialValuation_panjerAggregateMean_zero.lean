-- Prove2me | Theorems.Thm_ActuarialValuation_panjerAggregateMean_zero
-- name    : ActuarialValuation.panjerAggregateMean_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:57:21.462897+00:00
-- url     : https://prove2.me/theorems/f352da93-82a6-437c-a52f-477d6da94e12
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerAggregateMean_zero
-- statement:
--   The zero-loss probability contributes no expected aggregate cost. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   m_0=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateMean

namespace ActuarialValuation

theorem panjerAggregateMean_zero (g : ℕ → ℝ) : panjerAggregateMean g 0 = 0 := by sorry

end ActuarialValuation
