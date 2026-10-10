-- Prove2me | Theorems.Thm_ActuarialValuation_scrCovarianceTerm_nonneg
-- name    : ActuarialValuation.scrCovarianceTerm_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:13:05.162459+00:00
-- url     : https://prove2.me/theorems/5b407a33-e6ff-4327-bae3-b6c521789e26
-- title:
--   Two-module capital charges and correlation cross terms: scrCovarianceTerm_nonneg
-- statement:
--   Positive pairwise correlations and nonnegative capital charges give a nonnegative cross term. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \rho,C_1,C_2\ge0\Rightarrow T\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrCovarianceTerm

namespace ActuarialValuation

theorem scrCovarianceTerm_nonneg (rho a b : ℝ) (hr : 0 ≤ rho) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ scrCovarianceTerm rho a b := by sorry

end ActuarialValuation
