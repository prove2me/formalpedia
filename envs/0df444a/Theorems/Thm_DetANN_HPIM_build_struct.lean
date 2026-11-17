-- Prove2me | Theorems.Thm_DetANN_HPIM_build_struct
-- name    : DetANN.HPIM.build_struct
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T06:18:11.662081+00:00
-- url     : https://prove2.me/theorems/3e3fddd1-edfa-4cba-8ed0-4edb92ae6239
-- title:
--   Structure of the certified near-neighbour BSP
-- statement:
--   Let $P_1,\dots,P_n\in\mathbb R^m$, $r,c\in\mathbb R$, a fuel $f$ and a box $B=[lo,hi]$, and let $T=\mathrm{build}(f,B)$ (definition `DetANN_HPIMBuild`). Then:
--
--   1. the root of $T$ has the box $B$;
--   2. $T$ covers: at every cut, each point of the cut's box lies in the box of one of its two children;
--   3. if the recursion does not starve, every leaf of $T$ is certified:
--   $$\mathrm{OUT}\ \text{leaf } L:\ \mathrm{dist}(L,P_i)>r\ \ \forall i,\qquad \mathrm{IN}(i)\ \text{leaf } L:\ \mathrm{maxdist}(L,P_i)\le cr.$$
--
--   This is the structural half of the size bound for the certified BSP in the floor-free proof of `DetANN.lemma_3_3`. What remains is the counting half: at the fuel $\lceil n(2^{12}/\varepsilon)^{2m}\rceil+1$ the recursion does not starve from the root box, and the tree has at most twice that many nodes, independently of the spread of the points.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). It replaces the grids of Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, which need a floor operation.

import Mathlib
import Definitions.Def_DetANN_HPIMBuild

namespace DetANN.HPIM

/-- **Structure of the certified near-neighbour BSP.** For all points `pts`, radius `r`, factor `c`,
fuel `f` and box `[lo, hi]`, the BSP `T = build pts r c f lo hi` has the root box `[lo, hi]`, the
children of each of its cuts cover the cut's box, and, unless the recursion starves, every leaf of `T`
is certified: an `OUT` leaf is farther than `r` from every point, an `IN(i)` leaf lies within `c r`
of point `i`. -/
theorem build_struct {m n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ) (f : ℕ) (lo hi : Fin m → ℝ) :
    (build pts r c f lo hi).box = (lo, hi) ∧ (build pts r c f lo hi).Covers ∧
      (¬ Starves pts r c f lo hi → (build pts r c f lo hi).Certified pts r c) := by sorry

end DetANN.HPIM
