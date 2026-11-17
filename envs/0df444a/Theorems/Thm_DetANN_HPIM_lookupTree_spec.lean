-- Prove2me | Theorems.Thm_DetANN_HPIM_lookupTree_spec
-- name    : DetANN.HPIM.lookupTree_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T06:37:00.921205+00:00
-- url     : https://prove2.me/theorems/a24fa13f-2517-42c7-9e68-b0adb590b871
-- title:
--   The lookup contract
-- statement:
--   Let $m\ge1$, let $P_1,\dots,P_n\in\mathbb R^m$ with $n\ge1$, $r>0$ and $\delta\in(0,1/2)$. The lookup structure $Z=\mathrm{lookupTree}(P,r,1+\delta/4)$ (definition `DetANN_HPIMTree`):
--   1. satisfies the near-neighbour contract at radius $r$ and factor $1+\delta/4$: an answer $i$ has $\|q-P_i\|\le(1+\delta/4)r$, and a null answer means $\|q-P_j\|>r$ for all $j$;
--   2. visits at most $5\lfloor\log_2(2F)\rfloor+7$ nodes at every query, where $F=\lceil n(2^{12}/\varepsilon)^{2m}\rceil+1$ and $\varepsilon=\delta/4$.
--
--   This is the interface between the certified BSPs and the HPIM search. The visit bound is $O(m\log(n/\delta))$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib
import Definitions.Def_DetANN_HPIMTree

namespace DetANN.HPIM

/-- **The lookup contract.** For `m ≥ 1`, `n ≥ 1` points `P_i ∈ ℝ^m`, `r > 0` and `δ ∈ (0, 1/2)`, the
lookup structure `lookupTree P r (1 + δ/4) δ` satisfies the near-neighbour contract at radius `r` and
factor `1 + δ/4`, and visits at most `5 ⌊log₂(2 · bspFuel n m δ)⌋ + 7` nodes at every query. -/
theorem lookupTree_spec {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n)
    (P : Fin n → EuclideanSpace ℝ (Fin m)) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    NearNbrSpec P r (1 + δ / 4) (lookupTree (fun i j => P i j) r (1 + δ / 4) δ) ∧
    ∀ q : Fin m → ℝ, (lookupTree (fun i j => P i j) r (1 + δ / 4) δ).visits q ≤
      5 * Nat.log 2 (2 * bspFuel n m δ) + 7 := by sorry

end DetANN.HPIM
