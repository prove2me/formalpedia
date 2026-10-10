-- Prove2me | Theorems.Thm_ActuarialValuation_panjerSeverityMass_succ
-- name    : ActuarialValuation.panjerSeverityMass_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:27:16.674475+00:00
-- url     : https://prove2.me/theorems/a905e399-7697-4096-af8c-ce7cdefd750b
-- title:
--   Finite claim-size severity and convolution: panjerSeverityMass_succ
-- statement:
--   Truncated severity mass extends by precisely one extra loss size. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M_{n+1}=M_n+f_{n+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerSeverityMass

namespace ActuarialValuation

theorem panjerSeverityMass_succ (f : ℕ → ℝ) (n : ℕ) : panjerSeverityMass f (n+1) = panjerSeverityMass f n + f (n+1) := by sorry

end ActuarialValuation
