-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_lemma_3
-- name    : ExponomialAssortment.FPTAS.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:15:22.299557+00:00
-- url     : https://prove2.me/theorems/c1982031-b6ca-4ff6-897a-55a64b763098
-- title:
--   Lemma 3 — Profitable-state utility interval
-- statement:
--   Every reachable profitable state, including the guessed initial state, has utility statistic between k_l δ−Δ and k_l δ+Δ, with Δ=log((4n/η)(p_max/p_min)). This is the printed claim, including its false lower bound.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
--   - encoding: p_min is the minimum nonzero price → an explicit positive-price witness; reason: this is the nontrivial branch where the source grid and logarithmic ratio are defined; all-zero data remain covered by the headline theorem
--   - encoding: states evaluated from S_f, with l selected beforehand → concrete Reachable and bestSingle predicates; reason: these encode the construction in §5.2, including the initial state itself
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Lemma 3, printed p. 19, PDF p. 20

import Definitions.Def_ExponomialAssortment_FPTAS_DP

namespace ExponomialAssortment.FPTAS

theorem lemma_3 (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (hη : 0 < η) (hp : ∃ i, 0 < I.price i)
    (l f : Fin n) (hl : bestSingle I η l) (hf : f ≠ I.outside)
    (s : State) (hr : Reachable I C η l f s) (hs : Profitable I η l s) :
    (kIndex I η l : ℝ) * delta n η - Delta I η ≤ s.utilitySum ∧
    s.utilitySum ≤ (kIndex I η l : ℝ) * delta n η + Delta I η := by sorry

end ExponomialAssortment.FPTAS
