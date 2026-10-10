-- Prove2me | Theorems.Thm_ActuarialValuation_panjerAggregateMean_succ
-- name    : ActuarialValuation.panjerAggregateMean_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T08:00:57.401983+00:00
-- url     : https://prove2.me/theorems/fb774d04-fd59-4ac9-824e-3871f4a3e068
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerAggregateMean_succ
-- statement:
--   Truncated expected aggregate claim cost increases by the new loss-size contribution. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   m_{n+1}=m_n+(n+1)g_{n+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateMean

namespace ActuarialValuation

theorem panjerAggregateMean_succ (g : ℕ → ℝ) (n : ℕ) : panjerAggregateMean g (n+1) = panjerAggregateMean g n + ((n+1 : ℕ) : ℝ) * g (n+1) := by sorry

end ActuarialValuation
