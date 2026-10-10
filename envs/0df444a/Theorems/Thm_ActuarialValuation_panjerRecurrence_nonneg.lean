-- Prove2me | Theorems.Thm_ActuarialValuation_panjerRecurrence_nonneg
-- name    : ActuarialValuation.panjerRecurrence_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:50:37.725815+00:00
-- url     : https://prove2.me/theorems/2db97f4f-d69b-4049-b5de-4d5479c03ba6
-- title:
--   Compound Poisson Panjer recurrence: panjerRecurrence_nonneg
-- statement:
--   The uniquely generated compound Poisson aggregate coefficients are nonnegative for nonnegative severity probabilities. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \lambda,f\ge0\Rightarrow g_k\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecurrenceLaw

namespace ActuarialValuation

theorem panjerRecurrence_nonneg (lambda : ℝ) (f g : ℕ → ℝ) (hl : 0 ≤ lambda) (hf : ∀ j, 0 ≤ f j) (hg : panjerRecurrenceLaw lambda f g) : ∀ k : ℕ, 0 ≤ g k := by sorry

end ActuarialValuation
