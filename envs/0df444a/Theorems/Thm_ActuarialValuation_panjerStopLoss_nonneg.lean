-- Prove2me | Theorems.Thm_ActuarialValuation_panjerStopLoss_nonneg
-- name    : ActuarialValuation.panjerStopLoss_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T08:02:01.918575+00:00
-- url     : https://prove2.me/theorems/14ca5433-f5c8-45f9-a219-cf049c85d8d0
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerStopLoss_nonneg
-- statement:
--   Stop-loss payouts and aggregate claim weights are nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_k\ge0\Rightarrow SL_n(d)\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerStopLoss

namespace ActuarialValuation

theorem panjerStopLoss_nonneg (g : ℕ → ℝ) (n : ℕ) (d : ℝ) (hg : ∀ k ∈ Finset.range (n+1), 0 ≤ g k) : 0 ≤ panjerStopLoss g n d := by sorry

end ActuarialValuation
