-- Prove2me | Theorems.Thm_ActuarialValuation_panjerUpperTail_balance
-- name    : ActuarialValuation.panjerUpperTail_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:52:21.181979+00:00
-- url     : https://prove2.me/theorems/eeec4056-e69d-4d06-b808-7c499f1d7242
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerUpperTail_balance
-- statement:
--   Observed cumulative mass and modelled tail complement reconcile algebraically. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_n+T_n=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateCDF
import Definitions.Def_actuarial_panjerUpperTail

namespace ActuarialValuation

theorem panjerUpperTail_balance (g : ℕ → ℝ) (n : ℕ) : panjerAggregateCDF g n + panjerUpperTail g n = 1 := by sorry

end ActuarialValuation
