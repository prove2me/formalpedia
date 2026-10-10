-- Prove2me | Theorems.Thm_ActuarialValuation_panjerStopLoss_mono_truncation
-- name    : ActuarialValuation.panjerStopLoss_mono_truncation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T08:02:24.579263+00:00
-- url     : https://prove2.me/theorems/70957981-e538-4a2f-9111-01f376dcf8aa
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerStopLoss_mono_truncation
-- statement:
--   Including a nonnegative newly observed aggregate-loss atom cannot reduce stop-loss value. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   SL_n(d)\le SL_{n+1}(d)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerStopLoss

namespace ActuarialValuation

theorem panjerStopLoss_mono_truncation (g : ℕ → ℝ) (n : ℕ) (d : ℝ) (hg : 0 ≤ g (n+1)) : panjerStopLoss g n d ≤ panjerStopLoss g (n+1) d := by sorry

end ActuarialValuation
