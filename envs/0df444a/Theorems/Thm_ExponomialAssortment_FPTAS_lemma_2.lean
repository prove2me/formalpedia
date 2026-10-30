-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_lemma_2
-- name    : ExponomialAssortment.FPTAS.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:13:44.915038+00:00
-- url     : https://prove2.me/theorems/ef127c0e-8708-48e3-8cd6-8e0e2e0bb41f
-- title:
--   Lemma 2 — Utility difference rounding bounds
-- statement:
--   For every assortment and product i, the rounded utility difference sum lies between the exact sum minus iδ and the exact sum plus iδ, where δ=η/(2n) and source indices start at one.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Lemma 2, printed p. 17, PDF p. 18

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

namespace ExponomialAssortment.FPTAS

theorem lemma_2 (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (hη : 0 < η)
    (S : Finset (Fin n)) (hS : Feasible I C S) (i : Fin n) :
    gapSum I.utility S i - (i.val + 1) * delta n η ≤ gapSum (roundedUtility I η) S i ∧
    gapSum (roundedUtility I η) S i ≤ gapSum I.utility S i + (i.val + 1) * delta n η := by sorry

end ExponomialAssortment.FPTAS
