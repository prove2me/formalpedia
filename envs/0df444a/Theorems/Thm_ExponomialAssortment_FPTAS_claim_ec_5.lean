-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_claim_ec_5
-- name    : ExponomialAssortment.FPTAS.claim_ec_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:14:12.595992+00:00
-- url     : https://prove2.me/theorems/844ea634-5b53-4fc3-b75a-a0557f2d65fc
-- title:
--   Claim EC.5 — Single contribution bounded by twice optimum
-- statement:
--   For every feasible assortment and every product, its nonnegative G_i p_i x_i term is at most twice the optimum true revenue under the same capacity constraint, including the sole-outside-option case.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Claim EC.5, printed p. ec8, PDF p. 42

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

namespace ExponomialAssortment.FPTAS

theorem claim_ec_5 (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n)
    (S T : Finset (Fin n)) (hS : Feasible I C S) (hT : Optimal I C T) (i : Fin n) :
    (if i ∈ S then coefficient I.utility S i * I.price i else 0) ≤ 2 * revenue I T := by sorry

end ExponomialAssortment.FPTAS
