-- Prove2me | Theorems.Thm_ActuarialValuation_panjerFrequencyPremium_nonneg
-- name    : ActuarialValuation.panjerFrequencyPremium_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:44:24.545766+00:00
-- url     : https://prove2.me/theorems/c4bd87ed-2b05-4bde-9ede-1103f09492c2
-- title:
--   Compound Poisson Panjer recurrence: panjerFrequencyPremium_nonneg
-- statement:
--   Expected aggregate annual cost is nonnegative under positive frequency and severity. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \lambda,\mu\ge0\Rightarrow\Pi\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerFrequencyPremium

namespace ActuarialValuation

theorem panjerFrequencyPremium_nonneg (lambda mean : ℝ) (hl : 0 ≤ lambda) (hm : 0 ≤ mean) : 0 ≤ panjerFrequencyPremium lambda mean := by sorry

end ActuarialValuation
