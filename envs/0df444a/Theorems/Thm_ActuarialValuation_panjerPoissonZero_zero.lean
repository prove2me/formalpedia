-- Prove2me | Theorems.Thm_ActuarialValuation_panjerPoissonZero_zero
-- name    : ActuarialValuation.panjerPoissonZero_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:37:23.727306+00:00
-- url     : https://prove2.me/theorems/784e3be8-fc26-4267-a27f-3d52d90d0700
-- title:
--   Compound Poisson Panjer recurrence: panjerPoissonZero_zero
-- statement:
--   Zero annual claim intensity produces certain zero aggregate loss. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e^0=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerPoissonZero

namespace ActuarialValuation

theorem panjerPoissonZero_zero  : panjerPoissonZero 0 = 1 := by sorry

end ActuarialValuation
