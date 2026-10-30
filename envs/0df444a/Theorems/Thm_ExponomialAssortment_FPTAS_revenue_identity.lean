-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_revenue_identity
-- name    : ExponomialAssortment.FPTAS.revenue_identity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:14:02.908785+00:00
-- url     : https://prove2.me/theorems/2e940e91-6342-498e-8183-f0e240766d59
-- title:
--   Section 2.3, equation (1) — Expected revenue representation
-- statement:
--   For every feasible assortment, the probabilistic expected revenue equals both the indexed choice expression and the signed contribution sum in equation (1).
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Section 2.3, equation (1), printed p. 8, PDF p. 9

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

namespace ExponomialAssortment.FPTAS

theorem revenue_identity (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (S : Finset (Fin n)) (hS : Feasible I C S) :
    revenue I S = indexedScore I S ∧ revenue I S = contributionScore I S := by sorry

end ExponomialAssortment.FPTAS
