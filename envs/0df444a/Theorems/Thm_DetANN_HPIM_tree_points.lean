-- Prove2me | Theorems.Thm_DetANN_HPIM_tree_points
-- name    : DetANN.HPIM.tree_points
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T07:49:43.360201+00:00
-- url     : https://prove2.me/theorems/a8f5a409-e345-4fb2-adac-c778e2eec43e
-- title:
--   Size of the HPIM tree
-- statement:
--   Let $m,N\in\mathbb N$ and let $Y_1,\dots,Y_N\in\mathbb R^m$ be distinct. Then
--   $$\mathrm{treePts}(Y,N+1,\{1,\dots,N\})\le4N\bigl(\lceil\log_2N\rceil+1\bigr).$$
--
--   Here $\mathrm{treePts}$ (definition `DetANN_HPIMPreBlocks`) is the total number of points over the HPIM tree of definition `DetANN_HPIMTree`, with the children of one node that have the same set counted once. The tree does not depend on $\delta$.
--
--   This bounds the space of the preprocessing. Every node on $n$ points stores $n\cdot(C/\delta)^{O(m)}\,\mathrm{polylog}$ cells, so the total is $N(C/\delta)^{O(m)}\,\mathrm{polylog}(N/\delta)$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7): the preprocessing program of DetANN.HPIM.hpim_preprocessing is assembled from these blocks. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMLayout

namespace DetANN.HPIM

open PNormReg PNormRegLib

/-- **Size of the HPIM tree.** For distinct points, the total number of points over the tree, with the
children of one node that have the same set counted once, is at most `4 N (⌈log₂ N⌉ + 1)`. -/
theorem tree_points {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (hY : Function.Injective Y) :
    treePts Y (N + 1) Finset.univ ≤ 4 * N * (Nat.clog 2 N + 1) := by sorry

end DetANN.HPIM
