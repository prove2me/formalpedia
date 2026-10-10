-- Prove2me | Theorems.Thm_ActuarialValuation_panjerConvolution_add_left
-- name    : ActuarialValuation.panjerConvolution_add_left
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:29:49.533489+00:00
-- url     : https://prove2.me/theorems/b19e9395-e2cd-411f-af0b-f8810847937e
-- title:
--   Finite claim-size severity and convolution: panjerConvolution_add_left
-- statement:
--   Finite claim convolution is distributive in its first severity operand. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   ((f+h)*g)_k=(f*g)_k+(h*g)_k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerConvolution

namespace ActuarialValuation

theorem panjerConvolution_add_left (f h g : ℕ → ℝ) (k : ℕ) : panjerConvolution (fun j => f j + h j) g k = panjerConvolution f g k + panjerConvolution h g k := by sorry

end ActuarialValuation
