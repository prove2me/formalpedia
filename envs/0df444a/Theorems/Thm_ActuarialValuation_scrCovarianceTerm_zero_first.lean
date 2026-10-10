-- Prove2me | Theorems.Thm_ActuarialValuation_scrCovarianceTerm_zero_first
-- name    : ActuarialValuation.scrCovarianceTerm_zero_first
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:12:50.89198+00:00
-- url     : https://prove2.me/theorems/4dbf3e3a-a38c-4e99-97a5-dbace2234872
-- title:
--   Two-module capital charges and correlation cross terms: scrCovarianceTerm_zero_first
-- statement:
--   An absent risk module has no covariance charge. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_1=0\Rightarrow T=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. European Union (2009), Solvency II Directive 2009/138/EC, Article 104 and Annex IV, https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32009L0138; Bank of England Prudential Regulation Authority (2024), Standard Formula Annexes, https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf. Parent topic: Correlation-based insurance capital aggregation, systematic cross terms, quadratic risk charges and diversification benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.bankofengland.co.uk/-/media/boe/files/prudential-regulation/policy-statement/2024/november/ps1524app7.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrCovarianceTerm

namespace ActuarialValuation

theorem scrCovarianceTerm_zero_first (rho b : ℝ) : scrCovarianceTerm rho 0 b = 0 := by sorry

end ActuarialValuation
