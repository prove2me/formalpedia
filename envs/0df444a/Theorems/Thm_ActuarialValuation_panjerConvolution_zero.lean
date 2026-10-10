-- Prove2me | Theorems.Thm_ActuarialValuation_panjerConvolution_zero
-- name    : ActuarialValuation.panjerConvolution_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:29:19.302905+00:00
-- url     : https://prove2.me/theorems/9c0b8ee3-8381-43a6-b8c6-09084c56f86a
-- title:
--   Finite claim-size severity and convolution: panjerConvolution_zero
-- statement:
--   The zero-loss convolution has one contribution. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (f*g)_0=f_0g_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerConvolution

namespace ActuarialValuation

theorem panjerConvolution_zero (f g : ℕ → ℝ) : panjerConvolution f g 0 = f 0 * g 0 := by sorry

end ActuarialValuation
