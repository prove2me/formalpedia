-- Prove2me | Theorems.Thm_ActuarialValuation_panjerFrequencyPremium_zero
-- name    : ActuarialValuation.panjerFrequencyPremium_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:44:07.064699+00:00
-- url     : https://prove2.me/theorems/4d864083-d60c-4a93-b879-c997ab4eb7f4
-- title:
--   Compound Poisson Panjer recurrence: panjerFrequencyPremium_zero
-- statement:
--   With no claims the pure aggregate premium is zero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Pi(0,\mu)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerFrequencyPremium

namespace ActuarialValuation

theorem panjerFrequencyPremium_zero (mean : ℝ) : panjerFrequencyPremium 0 mean = 0 := by sorry

end ActuarialValuation
