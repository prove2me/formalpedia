-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_lemma_1
-- name    : ExponomialAssortment.FPTAS.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:14:01.12749+00:00
-- url     : https://prove2.me/theorems/87d15b5b-0a2e-4e8d-a2ac-929bf80dd1ad
-- title:
--   Lemma 1 — Rounded average price bounds
-- statement:
--   For every feasible assortment, the rounded average trajectory exists. Every prefix average lies between its exact average and (1+θ) to the prefix length times that average, where θ=η/(2n³) and η>0.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
--   - encoding: rounded averages and objectives treated as defined → partial rounding graphs with existence in conclusions; reason: the printed grid has no ceiling on some legal inputs; preserving asserted definedness exposes I1 without adding a hypothesis or endpoint
--   - encoding: p_min is the minimum nonzero price → an explicit positive-price witness; reason: this is the nontrivial branch where the source grid and logarithmic ratio are defined; all-zero data remain covered by the headline theorem
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Lemma 1, printed p. 15, PDF p. 16

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

namespace ExponomialAssortment.FPTAS

theorem lemma_1 (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (hη : 0 < η) (hp : ∃ i, 0 < I.price i)
    (S : Finset (Fin n)) (hS : Feasible I C S) :
    ∃ a, AverageTrajectory I η S a ∧ ∀ i : Fin n,
      average I S i.val ≤ a i.val ∧
      a i.val ≤ (1 + theta n η)^i.val * average I S i.val := by sorry

end ExponomialAssortment.FPTAS
