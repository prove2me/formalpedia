-- Prove2me | Theorems.Thm_ActuarialValuation_panjerSeverityMass_nonneg
-- name    : ActuarialValuation.panjerSeverityMass_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:27:27.337261+00:00
-- url     : https://prove2.me/theorems/36c306e1-b5ff-4d91-8e6a-39f673b94e7e
-- title:
--   Finite claim-size severity and convolution: panjerSeverityMass_nonneg
-- statement:
--   Nonnegative claim-severity weights yield a nonnegative truncated mass. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   f_k\ge0\Rightarrow M_n\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerSeverityMass

namespace ActuarialValuation

theorem panjerSeverityMass_nonneg (f : ℕ → ℝ) (n : ℕ) (h : ∀ k ∈ Finset.range (n+1), 0 ≤ f k) : 0 ≤ panjerSeverityMass f n := by sorry

end ActuarialValuation
