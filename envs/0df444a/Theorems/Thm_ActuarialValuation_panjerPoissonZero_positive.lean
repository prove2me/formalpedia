-- Prove2me | Theorems.Thm_ActuarialValuation_panjerPoissonZero_positive
-- name    : ActuarialValuation.panjerPoissonZero_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:35:03.16495+00:00
-- url     : https://prove2.me/theorems/7588c7b6-20b9-40e8-8e77-bc04868e8899
-- title:
--   Compound Poisson Panjer recurrence: panjerPoissonZero_positive
-- statement:
--   The Poisson probability of zero claims is strictly positive at finite intensity. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e^{-\lambda}>0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerPoissonZero

namespace ActuarialValuation

theorem panjerPoissonZero_positive (lambda : ℝ) : 0 < panjerPoissonZero lambda := by sorry

end ActuarialValuation
