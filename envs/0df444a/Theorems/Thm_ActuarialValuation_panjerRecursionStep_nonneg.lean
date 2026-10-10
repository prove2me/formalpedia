-- Prove2me | Theorems.Thm_ActuarialValuation_panjerRecursionStep_nonneg
-- name    : ActuarialValuation.panjerRecursionStep_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:40:55.035096+00:00
-- url     : https://prove2.me/theorems/f6af671c-ab54-495d-a1b9-4537aaaa8c12
-- title:
--   Compound Poisson Panjer recurrence: panjerRecursionStep_nonneg
-- statement:
--   Positive intensity and severities preserve nonnegative aggregate coefficient contributions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \lambda,f,g\ge0\Rightarrow\mathcal P_k(g)\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecursionStep

namespace ActuarialValuation

theorem panjerRecursionStep_nonneg (lambda : ℝ) (f g : ℕ → ℝ) (k : ℕ) (hl : 0 ≤ lambda) (hf : ∀ j, 0 ≤ f j) (hg : ∀ j, 0 ≤ g j) : 0 ≤ panjerRecursionStep lambda f g k := by sorry

end ActuarialValuation
