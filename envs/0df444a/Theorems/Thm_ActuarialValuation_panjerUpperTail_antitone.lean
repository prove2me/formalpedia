-- Prove2me | Theorems.Thm_ActuarialValuation_panjerUpperTail_antitone
-- name    : ActuarialValuation.panjerUpperTail_antitone
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:53:20.594689+00:00
-- url     : https://prove2.me/theorems/fd8107c5-3c95-469f-9959-a8780fd33f87
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerUpperTail_antitone
-- statement:
--   A nonnegative newly included loss atom reduces the remaining tail. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   T_{n+1}\le T_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerUpperTail

namespace ActuarialValuation

theorem panjerUpperTail_antitone (g : ℕ → ℝ) (n : ℕ) (h : 0 ≤ g (n+1)) : panjerUpperTail g (n+1) ≤ panjerUpperTail g n := by sorry

end ActuarialValuation
