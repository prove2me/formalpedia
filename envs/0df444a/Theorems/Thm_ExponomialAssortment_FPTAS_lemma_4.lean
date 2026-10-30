-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_lemma_4
-- name    : ExponomialAssortment.FPTAS.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:14:59.164195+00:00
-- url     : https://prove2.me/theorems/79f9fa6b-dc46-45ac-852e-bff4f87c5733
-- title:
--   Lemma 4 — Pruning retains the rounded optimum
-- statement:
--   For the first non-outside product of a joint rounded optimizer, a feasible pruned optimizer exists. Every such pruned optimizer attains the same value in the full rounded objective and at least (1−η) times the unpruned optimum.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
--   - encoding: rounded averages and objectives treated as defined → partial rounding graphs with existence in conclusions; reason: the printed grid has no ceiling on some legal inputs; preserving asserted definedness exposes I1 without adding a hypothesis or endpoint
--   - encoding: p_min is the minimum nonzero price → an explicit positive-price witness; reason: this is the nontrivial branch where the source grid and logarithmic ratio are defined; all-zero data remain covered by the headline theorem
--   - encoding: an optimal assortment and its computed objective → attainment and successful definedness made explicit; reason: the source claims an evaluated finite dynamic program; existence must not be hidden in a vacuous optimizer hypothesis
--   - encoding: x-hat optimizes the guessed pruned program and has its full rounded score → the conclusion also states equality of the pruned value and full rounded score; reason: Appendix B.8 explicitly asserts this equality; f is the first non-outside product of the rounded optimum
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Lemma 4, printed p. 19, PDF p. 20

import Definitions.Def_ExponomialAssortment_FPTAS_DP

namespace ExponomialAssortment.FPTAS

theorem lemma_4 (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (hη : 0 < η) (hp : ∃ i, 0 < I.price i)
    (l f : Fin n) (hl : bestSingle I η l)
    (T : Finset (Fin n)) (w : ℝ) (hT : RoundedOptimal I C η true T w)
    (hf : firstProduct I T f) :
    (∃ S v, PrunedOptimal I C η l f S v) ∧
    ∀ S v, PrunedOptimal I C η l f S v →
      RoundedScore I η true S v ∧ (1 - η) * w ≤ v := by sorry

end ExponomialAssortment.FPTAS
