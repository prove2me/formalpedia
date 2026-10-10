-- Prove2me | Theorems.Thm_ActuarialValuation_panjerAggregateCDF_mono
-- name    : ActuarialValuation.panjerAggregateCDF_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:52:01.954444+00:00
-- url     : https://prove2.me/theorems/09c6a878-6b8e-4702-8337-ccf57c50f5e0
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerAggregateCDF_mono
-- statement:
--   Cumulative aggregate claims probabilities cannot fall when added masses are nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_{n+1}\ge0\Rightarrow G_{n+1}\ge G_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateCDF

namespace ActuarialValuation

theorem panjerAggregateCDF_mono (g : ℕ → ℝ) (n : ℕ) (h : 0 ≤ g (n+1)) : panjerAggregateCDF g n ≤ panjerAggregateCDF g (n+1) := by sorry

end ActuarialValuation
