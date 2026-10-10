-- Prove2me | Theorems.Thm_ActuarialValuation_panjerConvolution_left_zero
-- name    : ActuarialValuation.panjerConvolution_left_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:29:36.770512+00:00
-- url     : https://prove2.me/theorems/39c908d8-9cb2-454b-99a8-914ef56f1e09
-- title:
--   Finite claim-size severity and convolution: panjerConvolution_left_zero
-- statement:
--   Zero claim mass produces zero convolution at every lattice point. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (0*g)_k=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerConvolution

namespace ActuarialValuation

theorem panjerConvolution_left_zero (g : ℕ → ℝ) (k : ℕ) : panjerConvolution (fun _ => (0 : ℝ)) g k = 0 := by sorry

end ActuarialValuation
