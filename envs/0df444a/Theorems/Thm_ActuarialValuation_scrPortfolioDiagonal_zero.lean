-- Prove2me | Theorems.Thm_ActuarialValuation_scrPortfolioDiagonal_zero
-- name    : ActuarialValuation.scrPortfolioDiagonal_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:40.483545+00:00
-- url     : https://prove2.me/theorems/50123edd-57f3-4904-a9bc-a2847e9dc090
-- title:
--   Finite-dimensional standard formula quadratic aggregation: scrPortfolioDiagonal_zero
-- statement:
--   Empty module universe has no diagonal charges. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_0=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPortfolioDiagonal

namespace ActuarialValuation

theorem scrPortfolioDiagonal_zero (c : ℕ → ℝ) : scrPortfolioDiagonal c 0 = 0 := by sorry

end ActuarialValuation
