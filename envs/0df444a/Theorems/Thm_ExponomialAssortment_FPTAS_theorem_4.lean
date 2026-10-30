-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_theorem_4
-- name    : ExponomialAssortment.FPTAS.theorem_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:13:49.639898+00:00
-- url     : https://prove2.me/theorems/aa3e471e-d9a6-4830-9052-e29865f371a9
-- title:
--   Theorem 4 — Joint discretization approximation
-- statement:
--   All feasible assortments have defined rounded scores, a joint rounded optimum is attained, and every joint rounded optimizer earns true revenue at least (1−η)³ times every true optimum.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
--   - encoding: rounded averages and objectives treated as defined → partial rounding graphs with existence in conclusions; reason: the printed grid has no ceiling on some legal inputs; preserving asserted definedness exposes I1 without adding a hypothesis or endpoint
--   - encoding: p_min is the minimum nonzero price → an explicit positive-price witness; reason: this is the nontrivial branch where the source grid and logarithmic ratio are defined; all-zero data remain covered by the headline theorem
--   - encoding: an optimal assortment and its computed objective → attainment and successful definedness made explicit; reason: the source claims an evaluated finite dynamic program; existence must not be hidden in a vacuous optimizer hypothesis
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Theorem 4, printed p. 17, PDF p. 18

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

namespace ExponomialAssortment.FPTAS

theorem theorem_4 (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (hη : 0 < η) (hp : ∃ i, 0 < I.price i) :
    TotalRounded I C η ∧ (∃ S v, RoundedOptimal I C η true S v) ∧
    ∀ S v T, RoundedOptimal I C η true S v → Optimal I C T →
      (1 - η)^3 * revenue I T ≤ revenue I S := by sorry

end ExponomialAssortment.FPTAS
