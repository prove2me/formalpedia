-- Prove2me | Theorems.Thm_ActuarialValuation_panjerSeverityMean_succ
-- name    : ActuarialValuation.panjerSeverityMean_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:28:18.339892+00:00
-- url     : https://prove2.me/theorems/9096ee7f-adf4-43ec-85e6-b816edb5b331
-- title:
--   Finite claim-size severity and convolution: panjerSeverityMean_succ
-- statement:
--   Increasing the severity truncation adds the new size-weighted term. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \mu_{n+1}=\mu_n+(n+1)f_{n+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerSeverityMean

namespace ActuarialValuation

theorem panjerSeverityMean_succ (f : ℕ → ℝ) (n : ℕ) : panjerSeverityMean f (n+1) = panjerSeverityMean f n + ((n+1 : ℕ) : ℝ) * f (n+1) := by sorry

end ActuarialValuation
