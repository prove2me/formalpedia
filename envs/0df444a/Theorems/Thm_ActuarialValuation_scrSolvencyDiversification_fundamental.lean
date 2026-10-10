-- Prove2me | Theorems.Thm_ActuarialValuation_scrSolvencyDiversification_fundamental
-- name    : ActuarialValuation.scrSolvencyDiversification_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:18.586976+00:00
-- url     : https://prove2.me/theorems/0a344b3f-3e01-43d8-9d2b-72c87bb1e137
-- title:
--   Finite-dimensional standard formula quadratic aggregation: scrSolvencyDiversification_fundamental
-- statement:
--   The capstone proves nonnegative two-module correlation aggregation, exact squared diversification reconciliation and the full-correlation limit. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q_\rho\ge0,\;D^2\ge0,\;Q_\rho+D^2=(C_1+C_2)^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared
import Definitions.Def_actuarial_scrSumSquared
import Definitions.Def_actuarial_scrDiversificationSquared

namespace ActuarialValuation

theorem scrSolvencyDiversification_fundamental (rho a b : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) : (0 ≤ scrPairSquared rho a b) ∧ (0 ≤ scrDiversificationSquared rho a b) ∧ (scrPairSquared rho a b + scrDiversificationSquared rho a b = scrSumSquared a b) ∧ (scrPairSquared 1 a b = scrSumSquared a b) := by sorry

end ActuarialValuation
