-- Prove2me | Theorems.Thm_ActuarialValuation_scrPortfolioQuadratic_nonneg
-- name    : ActuarialValuation.scrPortfolioQuadratic_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:42.567782+00:00
-- url     : https://prove2.me/theorems/c707840e-b496-4073-bc84-f72d296d73a2
-- title:
--   Finite-dimensional standard formula quadratic aggregation: scrPortfolioQuadratic_nonneg
-- statement:
--   Nonnegative charges and coefficients give nonnegative aggregate quadratic risk. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_i,\rho_{ij}\ge0\Rightarrow Q_n\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPortfolioQuadratic

namespace ActuarialValuation

theorem scrPortfolioQuadratic_nonneg (c : ℕ → ℝ) (rho : ℕ → ℕ → ℝ) (n : ℕ) (hc : ∀ i ∈ Finset.range n, 0 ≤ c i) (hr : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, 0 ≤ rho i j) : 0 ≤ scrPortfolioQuadratic c rho n := by sorry

end ActuarialValuation
