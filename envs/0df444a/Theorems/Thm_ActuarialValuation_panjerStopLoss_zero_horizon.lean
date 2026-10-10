-- Prove2me | Theorems.Thm_ActuarialValuation_panjerStopLoss_zero_horizon
-- name    : ActuarialValuation.panjerStopLoss_zero_horizon
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T08:01:15.979669+00:00
-- url     : https://prove2.me/theorems/60c9e1c8-3871-4145-baa7-64a48b215286
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerStopLoss_zero_horizon
-- statement:
--   A nonnegative retention yields zero reimbursement if only zero-loss outcomes are included. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL_0(d)=0\;d\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerStopLoss

namespace ActuarialValuation

theorem panjerStopLoss_zero_horizon (g : ℕ → ℝ) (d : ℝ) (hd : 0 ≤ d) : panjerStopLoss g 0 d = 0 := by sorry

end ActuarialValuation
