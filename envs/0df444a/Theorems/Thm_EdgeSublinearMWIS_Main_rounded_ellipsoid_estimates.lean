-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_rounded_ellipsoid_estimates
-- name    : EdgeSublinearMWIS.Main.rounded_ellipsoid_estimates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:29:10.672866+00:00
-- url     : https://prove2.me/theorems/8e2efda7-2ea3-4b39-8a4f-cff9458f73ef
-- title:
--   Rounded ellipsoid sequences: containment, conditioning, contraction and bit bounds
-- statement:
--   Let $n\ge2$ and let $a_k\in\mathbb Q^n$ be cut normals satisfying $\|a_k\|_2^2\ge1$. Write $A_k$ and $c_k(c_0)$ for the stored rational shape and center sequences defined by the prescribed dyadic rounding scheme, starting at $A_0=I$ and the rational center $c_0$.
--
--   The iterates remain positive definite and satisfy, for every real vector $z$,
--   $$2^{-2k}\|z\|_2^2\le z^T A_k z\le4^k\|z\|_2^2.$$
--   If a point starts in the initial unit ball and satisfies every central cut before time $k$, it remains in the stored ellipsoid:
--   $$\|x-c_0\|_2^2\le1,\quad a_j^T(x-c_j(c_0))\le0\ (j<k)
--   \quad\Longrightarrow\quad
--   (x-c_k(c_0))^T A_k^{-1}(x-c_k(c_0))\le1.$$
--   For every natural number $B$, the explicit budget gives
--   $$\sqrt{\det A_{4(n+1)(Bn+1)}}<2^{-Bn}.$$
--   Every numerator and denominator of $A_k$ and of $c_k(0)$ has magnitude at most
--   $$2^{10(k+n+4)}.$$
--   The entrywise magnitude bounds are $|(A_k)_{ij}|\le4^k$ and $|c_k(0)_i|\le2^{k+2}$.
--
--   Together these estimates justify exact dimension reduction and polynomial bit complexity for the same rational ellipsoid updates. They concern arbitrary supplied central-cut normals and do not assume a separation oracle or an LP solver.
-- source:
--   Edouard Bonnet, Linear-programming foundations, immutable source https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs, EllipsoidSequence.lean (shapes_invariant, preserves_points_up_to, shapes_below_threshold), EllipsoidStateSize.lean (centers_magnitude, shapes_entry_magnitude and denominator bounds); dyadic height corollaries for the same stored iterates. Supporting the exact-feasibility step in Bonnet--Chang, Theorem 2, Section 5.

import Definitions.Def_EdgeSublinearMWIS_Main_RationalEllipsoids
open scoped BigOperators
open Matrix EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.GLS.Cast

theorem EdgeSublinearMWIS.Main.rounded_ellipsoid_estimates (n : ℕ) (hn : 2 ≤ n)
    (a : ℕ → Fin n → ℚ) (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) :
    RoundedEllipsoidEstimates n a := by sorry
