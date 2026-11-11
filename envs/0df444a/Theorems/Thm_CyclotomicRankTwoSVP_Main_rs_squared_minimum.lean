-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_rs_squared_minimum
-- name    : CyclotomicRankTwoSVP.Main.rs_squared_minimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:09.200433+00:00
-- url     : https://prove2.me/theorems/c3d6b704-77c3-42cc-a9bd-640686c4f768
-- title:
--   Lemma 3.1 — Reed–Solomon squared minimum
-- statement:
--   For every prime $q$ and integer $1\le k\le q/2$, the Construction A Reed–Solomon lattice $L_{q,k}=\{z\in\mathbb Z^{\mathbb F_q}:H_q(k)z=0\}$ satisfies
--
--   $$\lambda_1(L_{q,k})^2\ge2k.$$
--
--   Its norm here is the coefficient Euclidean norm, not the canonical field norm. The result includes $k=1$ and the endpoint $2k=q$, and states the full squared lower bound rather than a natural-radius approximation. It supplies the lattice minimum used for the principal ideal.
--
--   Differences from the source:
--   - encoding: the squared attained first minimum of the indicated lattice → the real infimum of its nonzero squared norm values; reason: these nonzero discrete lattices have a shortest vector; the set of values is nonempty and bounded below by zero
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 9 / PDF p. 10, Lemma 3.1

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem rs_squared_minimum (q k : ℕ) [Fact q.Prime]
    (hk : 1 ≤ k) (hkq : 2 * k ≤ q) :
    firstSquared coeffNorm (RSLattice q k : Set (ZMod q → ℤ)) ≥ 2 * k := by sorry

end CyclotomicRankTwoSVP.Main
