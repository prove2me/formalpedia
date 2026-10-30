-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_claim_ec_3
-- name    : ExponomialAssortment.FPTAS.claim_ec_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:13:50.872866+00:00
-- url     : https://prove2.me/theorems/86b2bda0-0f8e-4d55-9c53-b1160cbb063b
-- title:
--   Claim EC.3 — Rounded price objective underestimates revenue
-- statement:
--   For every feasible assortment, the price-rounded score is defined and is at most its true expected revenue.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
--   - encoding: rounded averages and objectives treated as defined → partial rounding graphs with existence in conclusions; reason: the printed grid has no ceiling on some legal inputs; preserving asserted definedness exposes I1 without adding a hypothesis or endpoint
--   - encoding: p_min is the minimum nonzero price → an explicit positive-price witness; reason: this is the nontrivial branch where the source grid and logarithmic ratio are defined; all-zero data remain covered by the headline theorem
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Claim EC.3, printed p. ec7, PDF p. 41

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

namespace ExponomialAssortment.FPTAS

theorem claim_ec_3 (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (hη : 0 < η) (hp : ∃ i, 0 < I.price i)
    (S : Finset (Fin n)) (hS : Feasible I C S) :
    ∃ v, RoundedScore I η false S v ∧ v ≤ revenue I S := by sorry

end ExponomialAssortment.FPTAS
