-- Prove2me | Theorems.Thm_ActuarialValuation_panjerRecurrence_unique
-- name    : ActuarialValuation.panjerRecurrence_unique
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:49:42.173675+00:00
-- url     : https://prove2.me/theorems/6058e4f6-d291-45ed-b250-ab734b31ba67
-- title:
--   Compound Poisson Panjer recurrence: panjerRecurrence_unique
-- statement:
--   A Poisson zero-mass initial condition plus the forward Panjer recurrence uniquely determines all lattice coefficients. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_0=h_0,\;\mathcal P(g)=\mathcal P(h)\Rightarrow g=h
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecurrenceLaw

namespace ActuarialValuation

theorem panjerRecurrence_unique (lambda : ℝ) (f g h : ℕ → ℝ) (hg : panjerRecurrenceLaw lambda f g) (hh : panjerRecurrenceLaw lambda f h) : ∀ k : ℕ, g k = h k := by sorry

end ActuarialValuation
