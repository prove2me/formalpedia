-- Prove2me | Theorems.Thm_ActuarialValuation_scrPairShift_zero
-- name    : ActuarialValuation.scrPairShift_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:14.67301+00:00
-- url     : https://prove2.me/theorems/61291b74-3ab9-4523-90c8-4c3e148bda82
-- title:
--   Diversification gains and pairwise correlation bounds: scrPairShift_zero
-- statement:
--   A zero change in module capital leaves aggregate squared risk unchanged. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q(C_1+0,C_2)=Q(C_1,C_2)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared
import Definitions.Def_actuarial_scrPairShift

namespace ActuarialValuation

theorem scrPairShift_zero (rho a b : ℝ) : scrPairShift rho a b 0 = scrPairSquared rho a b := by sorry

end ActuarialValuation
