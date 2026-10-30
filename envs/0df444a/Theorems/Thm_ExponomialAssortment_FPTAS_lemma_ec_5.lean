-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_lemma_ec_5
-- name    : ExponomialAssortment.FPTAS.lemma_ec_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:13:53.069656+00:00
-- url     : https://prove2.me/theorems/b917819b-6d07-4e5c-9494-97bcb1d393ce
-- title:
--   Lemma EC.5 — Two-sided comparison after utility discretization
-- statement:
--   For every feasible assortment the rounded average trajectory exists, and its joint rounded score lies between (1−η) and (1+η) times its price-only rounded score. Both scores are signed sums.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
--   - encoding: rounded averages and objectives treated as defined → partial rounding graphs with existence in conclusions; reason: the printed grid has no ceiling on some legal inputs; preserving asserted definedness exposes I1 without adding a hypothesis or endpoint
--   - encoding: p_min is the minimum nonzero price → an explicit positive-price witness; reason: this is the nontrivial branch where the source grid and logarithmic ratio are defined; all-zero data remain covered by the headline theorem
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Lemma EC.5, printed p. ec9, PDF p. 43

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

namespace ExponomialAssortment.FPTAS

theorem lemma_ec_5 (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (hη : 0 < η) (hp : ∃ i, 0 < I.price i)
    (S : Finset (Fin n)) (hS : Feasible I C S) :
    ∃ a, AverageTrajectory I η S a ∧
      (1 - η) * score I I.utility S a ≤ score I (roundedUtility I η) S a ∧
      score I (roundedUtility I η) S a ≤ (1 + η) * score I I.utility S a := by sorry

end ExponomialAssortment.FPTAS
