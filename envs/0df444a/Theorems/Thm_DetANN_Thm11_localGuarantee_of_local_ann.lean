-- Prove2me | Theorems.Thm_DetANN_Thm11_localGuarantee_of_local_ann
-- name    : DetANN.Thm11.localGuarantee_of_local_ann
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:41.476333+00:00
-- url     : https://prove2.me/theorems/c706d82d-516f-4b1e-9dda-0093a267372d
-- title:
--   Local ANN answers lift to the guarantee (25) for every original point
-- statement:
--   For every tuple $v$, let $r_v$ index a $(1+\varepsilon/100)$-approximate nearest-neighbor answer in the deduplicated projected database `localData`. Map this local answer back to the original database by the chosen representative $x_v=\operatorname{localRepIdx}(r_v)$. Then the padded original points $\bar P_{x_v}$ satisfy the squared local guarantee (25):
--   $$
--   \|\mathcal A_v(q-\bar P_{x_v})\|_2^2
--    \le (1+\varepsilon/100)^2\|\mathcal A_v(q-y)\|_2^2
--   $$
--   for every $v$ and every $y$ in the padded original set. In particular, comparison against an original point whose projection was discarded by deduplication is still valid. This is precisely the `LocalGuarantee` conjunct of `LocalAnswer`.
--
--   The result needs no assumption that $\operatorname{annReps}>0$, no injectivity of the superblock projections, and no separate treatment of $n=1$.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §7.1, p.17, equation (25): the local structures are queried on the projected dataset $\{\mathcal A_vx:x\in P\}$ and their answers are original points $x_v\in P$. Deduplication with representatives is the formal device used to meet the injective-list hypothesis of Lemma 3.3, p.7.

import Mathlib
import Definitions.Def_DetANN_Thm11_LocalProjection

/-- Inner ANN answers on the deduplicated local databases give the local guarantee (25) for every
original padded point. -/
theorem DetANN.Thm11.localGuarantee_of_local_ann {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (q : EuclideanSpace ℝ (Fin (2 ^ k)))
    (r : ∀ v : Fin (2 ^ k), Fin (projectedSet C₀ k P ε v).card)
    (hr : ∀ (v : Fin (2 ^ k)) (a : Fin (projectedSet C₀ k P ε v).card),
      ‖annProject C₀ k P ε v q - localData C₀ k P ε v (r v)‖ ≤
        (1 + ε / 100) * ‖annProject C₀ k P ε v q - localData C₀ k P ε v a‖) :
    LocalGuarantee (annBlocks C₀ k P ε) (annTuples k ε) (paddedSet k P) q
      (fun v => padVec (2 ^ k) (P (localRepIdx C₀ k P ε v (r v)))) (1 + ε / 100) := by sorry
