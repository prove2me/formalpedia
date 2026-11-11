-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_sparse_multiplicity
-- name    : CyclotomicRankTwoSVP.Main.sparse_multiplicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:19.881484+00:00
-- url     : https://prove2.me/theorems/817cc6d7-a2b2-41ee-b18b-7ecf92961660
-- title:
--   Lemma 3.6 — sparse polynomial multiplicity
-- statement:
--   Let $q$ be an odd prime and let $F(X)=\sum_{i=1}^s c_iX^{a_i}\in\mathbb F_q[X]$ be nonzero, with every $c_i\ne0$ and pairwise distinct exponents $a_i\in\{0,\ldots,q-1\}$. Then
--
--   $$\operatorname{ord}_{X=1}F\le s-1.$$
--
--   The coefficients are arbitrary nonzero field elements and the number of terms is arbitrary. The nonzero-polynomial hypothesis excludes $s=0$, so natural subtraction does not alter the bound. This supplies the multiplicity constraint used for ideal-coset separation.
--
--   Differences from the source:
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 13 / PDF p. 14, Lemma 3.6

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem sparse_multiplicity (q s : ℕ) [Fact q.Prime] (hq : Odd q)
    (a : Fin s → Fin q) (ha : Function.Injective a) (c : Fin s → ZMod q)
    (hc : ∀ i, c i ≠ 0)
    (hF : (∑ i, Polynomial.monomial (a i).val (c i)) ≠ 0) :
    Polynomial.rootMultiplicity (1 : ZMod q) (∑ i, Polynomial.monomial (a i).val (c i)) ≤ s - 1 := by sorry

end CyclotomicRankTwoSVP.Main
