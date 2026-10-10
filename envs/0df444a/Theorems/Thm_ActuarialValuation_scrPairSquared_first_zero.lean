-- Prove2me | Theorems.Thm_ActuarialValuation_scrPairSquared_first_zero
-- name    : ActuarialValuation.scrPairSquared_first_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:58.396545+00:00
-- url     : https://prove2.me/theorems/36e91c31-fa09-448d-92c4-ce1e533b7c83
-- title:
--   Diversification gains and pairwise correlation bounds: scrPairSquared_first_zero
-- statement:
--   When one risk capital charge is zero, only the other diagonal charge remains. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q(0,C_2)=C_2^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared

namespace ActuarialValuation

theorem scrPairSquared_first_zero (rho b : ℝ) : scrPairSquared rho 0 b = b^2 := by sorry

end ActuarialValuation
