-- Prove2me | Theorems.Thm_ActuarialValuation_panjerAggregateClaims_fundamental
-- name    : ActuarialValuation.panjerAggregateClaims_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T08:02:55.399642+00:00
-- url     : https://prove2.me/theorems/b7a89ffa-8add-4065-8ec3-d3b6d9688629
-- title:
--   Finite aggregate loss reserve and stop-loss valuation: panjerAggregateClaims_fundamental
-- statement:
--   The compound aggregate-claims capstone combines genuine uniqueness of forward Panjer probabilities, nonnegative aggregate coefficients, and finite claim-payment cost controls. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g=h,\;g_k\ge0,\;G_n+T_n=1,\;SL_n(d)\ge0,\;\lambda\mu_n\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer, Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12 (1981), pp. 22-26, https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf; Sundt and Jewell, Further Results on Recursive Evaluation of Compound Distributions, ASTIN Bulletin 12 (1981), https://www.casact.org/sites/default/files/database/astin_vol12no1_27.pdf. Parent topic: Finite lattice claim severities, compound Poisson aggregate claim coefficients and Panjer recurrence with strictly positive claim sizes. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol12no1_22.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerSeverityMean
import Definitions.Def_actuarial_panjerRecurrenceLaw
import Definitions.Def_actuarial_panjerFrequencyPremium
import Definitions.Def_actuarial_panjerAggregateCDF
import Definitions.Def_actuarial_panjerUpperTail
import Definitions.Def_actuarial_panjerStopLoss

namespace ActuarialValuation

theorem panjerAggregateClaims_fundamental (lambda : ℝ) (f g h : ℕ → ℝ) (hl : 0 ≤ lambda) (hf : ∀ j, 0 ≤ f j) (hfzero : f 0 = 0) (hg : panjerRecurrenceLaw lambda f g) (hh : panjerRecurrenceLaw lambda f h) (n : ℕ) (d : ℝ) : (∀ k : ℕ, g k = h k) ∧ (∀ k : ℕ, 0 ≤ g k) ∧ (panjerAggregateCDF g n + panjerUpperTail g n = 1) ∧ (0 ≤ panjerStopLoss g n d) ∧ (0 ≤ panjerFrequencyPremium lambda (panjerSeverityMean f n)) := by sorry

end ActuarialValuation
