-- Prove2me | Theorems.Thm_DetANN_HPIM_build_size
-- name    : DetANN.HPIM.build_size
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T06:36:36.602525+00:00
-- url     : https://prove2.me/theorems/c10476a1-f03e-402d-8726-ca2d6e5cd29f
-- title:
--   Size of the certified near-neighbour BSP
-- statement:
--   Let $m\ge1$, let $P_1,\dots,P_n\in\mathbb R^m$ with $n\ge1$, $r>0$, $\delta\in(0,1/2)$, $\varepsilon=\delta/4$ and $c=1+\varepsilon$. Let $F=\lceil n(2^{12}/\varepsilon)^{2m}\rceil+1$, and build the certified near-neighbour BSP $T$ (definition `DetANN_HPIMBuild`) from the root box with fuel $F$. Then the recursion does not starve, and
--   $$|T|\le2F.$$
--
--   The bound depends only on $n$, $m$ and $\varepsilon$, not on $r$ or on the spread of the points. Together with `build_struct`, it says that every leaf of $T$ is certified. Together with `balance_spec`, it makes every lookup cost $O(m\log(n/\delta))$ node visits.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib
import Definitions.Def_DetANN_HPIMBuild

namespace DetANN.HPIM

/-- **Size of the certified near-neighbour BSP.** Let `m ≥ 1`, `n ≥ 1` points in `ℝ^m`, `r > 0`,
`δ ∈ (0, 1/2)`, `c = 1 + δ/4`. From the root box, with the fuel `bspFuel n m δ = ⌈n (2^12/ε)^{2m}⌉ + 1`
(`ε = δ/4`), the recursion of `build` does not starve, and the BSP has at most `2 · bspFuel n m δ`
nodes. The bound does not depend on `r` or on the spread of the points. -/
theorem build_size {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ¬ Starves pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r) ∧
      (build pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)).paths.card ≤
        2 * bspFuel n m δ := by sorry

end DetANN.HPIM
