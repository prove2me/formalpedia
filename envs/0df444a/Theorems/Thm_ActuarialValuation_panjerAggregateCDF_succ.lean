-- Prove2me | Theorems.Thm_ActuarialValuation_panjerAggregateCDF_succ
-- name    : ActuarialValuation.panjerAggregateCDF_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:51:47.675973+00:00
-- url     : https://prove2.me/theorems/e596b50e-cb77-4063-93b8-72e5df299314
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerAggregateCDF_succ
-- statement:
--   Each additional lattice coefficient increases the finite cumulative probability by that coefficient. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_{n+1}=G_n+g_{n+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateCDF

namespace ActuarialValuation

theorem panjerAggregateCDF_succ (g : ℕ → ℝ) (n : ℕ) : panjerAggregateCDF g (n+1) = panjerAggregateCDF g n + g (n+1) := by sorry

end ActuarialValuation
