-- Prove2me | Theorems.Thm_ActuarialValuation_scrPairSquared_zero
-- name    : ActuarialValuation.scrPairSquared_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:13:21.193639+00:00
-- url     : https://prove2.me/theorems/8d165d89-f114-4856-a65e-614359a7b2cf
-- title:
--   Two-module capital charges and correlation cross terms: scrPairSquared_zero
-- statement:
--   No module capital means no combined squared capital. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q(0,0)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared

namespace ActuarialValuation

theorem scrPairSquared_zero (rho : ℝ) : scrPairSquared rho 0 0 = 0 := by sorry

end ActuarialValuation
