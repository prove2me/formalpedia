-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_claim_ec_4
-- name    : ExponomialAssortment.FPTAS.claim_ec_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:13:39.517403+00:00
-- url     : https://prove2.me/theorems/e7a44464-887a-4c6a-a5e9-4c8e58dd0a62
-- title:
--   Claim EC.4 — Rounded price objective at the true optimum
-- statement:
--   At any true revenue optimizer, the price-rounded score is defined and at least (1−η) times the optimal true revenue.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
--   - encoding: rounded averages and objectives treated as defined → partial rounding graphs with existence in conclusions; reason: the printed grid has no ceiling on some legal inputs; preserving asserted definedness exposes I1 without adding a hypothesis or endpoint
--   - encoding: p_min is the minimum nonzero price → an explicit positive-price witness; reason: this is the nontrivial branch where the source grid and logarithmic ratio are defined; all-zero data remain covered by the headline theorem
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Claim EC.4, printed p. ec8, PDF p. 42

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

namespace ExponomialAssortment.FPTAS

theorem claim_ec_4 (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (hη : 0 < η) (hp : ∃ i, 0 < I.price i)
    (T : Finset (Fin n)) (hT : Optimal I C T) :
    ∃ v, RoundedScore I η false T v ∧ (1 - η) * revenue I T ≤ v := by sorry

end ExponomialAssortment.FPTAS
