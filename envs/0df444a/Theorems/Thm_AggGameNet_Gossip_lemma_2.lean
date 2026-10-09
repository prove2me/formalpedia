-- Prove2me | Theorems.Thm_AggGameNet_Gossip_lemma_2
-- name    : AggGameNet.Gossip.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:17.014977+00:00
-- url     : https://prove2.me/theorems/6714f372-7717-493d-91bb-5e5d12a23b68
-- title:
--   Lemma 2, p. 10 — mean estimate equals mean decision
-- statement:
--   Let $v_i^0=x_i^0$ and update each estimate by $v_i^{k+1}=\hat v_i^k+x_i^{k+1}-x_i^k$, where $\hat v^k$ is obtained by the pairwise gossip matrix. For every realization and every $k\ge0$,
--
--   $$
--   y^k:=\frac1N\sum_i v_i^k=\frac1N\sum_i x_i^k.
--   $$
--
--   This identity keeps the tracked average equal to the actual average throughout the gossip run.
--
--   **Formalization Note** The source assumes that every matrix has unit column sums. The displayed gossip matrix has that property directly, so the theorem specializes the lemma to this mission's matrices. Only the estimate recursion is assumed; no projected-gradient condition is needed.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 2, p. 10; gossip matrix (26), p. 16

import Mathlib
import Definitions.Def_AggGameNet_Gossip_Setting

open MeasureTheory Filter Finset
open scoped BigOperators

namespace AggGameNet.Gossip

theorem lemma_2 {N n : ℕ} (hN : 0 < N) {Ω : Type*}
    (I J : ℕ → Ω → Fin N)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (h0 : ∀ ω, v 0 ω = x 0 ω)
    (hrec : ∀ ω k i,
      v (k + 1) ω i = vhat I J v k ω i + x (k + 1) ω i - x k ω i) :
    ∀ ω k, yavg v k ω = (1 / (N : ℝ)) • ∑ i, x k ω i := by sorry

end AggGameNet.Gossip
