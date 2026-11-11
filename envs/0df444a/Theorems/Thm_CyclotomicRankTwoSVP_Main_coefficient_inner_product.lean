-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_coefficient_inner_product
-- name    : CyclotomicRankTwoSVP.Main.coefficient_inner_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:09.168381+00:00
-- url     : https://prove2.me/theorems/21c849f3-b718-422c-8dd8-f16bb798eea0
-- title:
--   Lemma 2.2 — canonical coefficient inner product and norm
-- statement:
--   Let $q$ be an odd prime. For every pair of rational coefficient vectors $x,y\in\mathbb Q^{\mathbb F_q}$,
--
--   $$\langle[x],[y]\rangle=q\sum_a x_ay_a-\left(\sum_a x_a\right)\left(\sum_a y_a\right).$$
--
--   For every integer vector $z\in\mathbb Z^{\mathbb F_q}$, both equalities hold:
--
--   $$N([z])=q\sum_a z_a^2-\left(\sum_a z_a\right)^2=\sum_{a<b}(z_a-z_b)^2.$$
--
--   The order in the last sum is the order of representatives $0,\ldots,q-1$. These identities relate the canonical norm to coefficient arithmetic, including the rational inner-product identity.
--
--   Differences from the source:
--   - encoding: K = Q(zeta_q), O_K = Z[zeta_q], all complex embeddings → a fixed isomorphic cyclotomic splitting field, the integer adjoin of its primitive root, and all rational algebra embeddings into C; reason: the same prime-conductor field and unnormalized canonical norm, with no additional source hypotheses
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 6 / PDF p. 7, Lemma 2.2; statement continues through printed p. 7 / PDF p. 8

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem coefficient_inner_product (q : ℕ) [Fact q.Prime] (hq : Odd q) :
    (∀ x y : ZMod q → ℚ,
      canonicalInner (evalQ x) (evalQ y) =
        q * (∑ a, (x a : ℝ) * (y a : ℝ)) - (∑ a, (x a : ℝ)) * (∑ a, (y a : ℝ))) ∧
    (∀ z : ZMod q → ℤ,
      N (evalZ z) = q * coeffNorm z - (coeffSum z : ℝ) ^ 2 ∧
      N (evalZ z) = ∑ a, ∑ b, if a.val < b.val then ((z a : ℝ) - z b) ^ 2 else 0) := by sorry

end CyclotomicRankTwoSVP.Main
