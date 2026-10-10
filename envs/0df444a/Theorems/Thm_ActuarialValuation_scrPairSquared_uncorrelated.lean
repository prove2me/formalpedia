-- Prove2me | Theorems.Thm_ActuarialValuation_scrPairSquared_uncorrelated
-- name    : ActuarialValuation.scrPairSquared_uncorrelated
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:13:33.237238+00:00
-- url     : https://prove2.me/theorems/ae03febd-9aa0-47e4-80f8-81948d808ed0
-- title:
--   Two-module capital charges and correlation cross terms: scrPairSquared_uncorrelated
-- statement:
--   At zero correlation, aggregation reduces to the diagonal-only sum. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q_0=C_1^2+C_2^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared
import Definitions.Def_actuarial_scrUncorrelatedSquared

namespace ActuarialValuation

theorem scrPairSquared_uncorrelated (a b : ℝ) : scrPairSquared 0 a b = scrUncorrelatedSquared a b := by sorry

end ActuarialValuation
