-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc
-- name    : AlgebraicCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/dd937934-63e4-5149-a2a1-bca73f9fc41c
-- title:
--   Interpolation on a rational function field with prescribed simple poles
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field that is an algebra over $k$, and suppose given a ring isomorphism $e : \mathrm{RatFunc}\,k \simeq F$ with $e(c) = c$ for every $c \in k$ (the two $k$-algebra structures agreeing under $e$). Here a place of $F$ over $k$ is a valuation subring of $F$ containing the image of $k$, different from $F$ itself, and a principal ideal ring; $\operatorname{ord}_v$ denotes $-\log$ of the associated $\mathbb{Z}^{m0}$-valued adic valuation, and $v.\mathrm{HasValue}\,g\,a$ means that $g$ lies in the valuation subring of $v$ and its residue equals the image of $a \in k$ in the residue field of $v$. Let $U$, $Z_v$, $Z_a$ be finite sets of such places, pairwise disjoint in the pairs $(U,Z_v)$, $(U,Z_a)$, $(Z_v,Z_a)$, let $t_0$ be a place lying in none of $U$, $Z_v$, $Z_a$, let $\beta \in k$, let $\mathrm{val}$ be an arbitrary $k$-valued function on places (read only on $Z_v$), and let $\mathrm{bad} \subset k$ be a finite set. Assume $\#Z_v + 1 \le \#U$. Then there exists $g \in F$ such that $g$ lies in the Riemann–Roch space of the divisor $\sum_{u \in U} u$, i.e. the adic valuation of $g$ at each place $v$ is at most $\exp$ of the coefficient of $v$ in that divisor (so $g$ has at most simple poles, all in $U$); $\operatorname{ord}_{t_0}(g - \beta) = 1$; $g$ has value $\mathrm{val}(z)$ at each $z \in Z_v$; and at each $z \in Z_a$ the function $g$ has some value $\gamma \in k$ with $\gamma \notin \mathrm{bad}$.
--
--   This is a genus-zero interpolation statement of Mittag-Leffler/Lagrange type on the projective line: a rational function with prescribed simple poles, prescribed values at finitely many places, a value $\beta$ attained to order exactly one at a further place, and values avoiding a prescribed finite set at finitely many other places. It is used in the construction of level-one prolongations of place specialisations on modular curves, notably by [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_commonUnit_ord_eq_one_of_mem_levelOne`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_commonUnit_ord_eq_one_of_mem_levelOne) and the two accompanying existence lemmas there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (U Zv Za : Finset (Place k F)) (t₀ : Place k F) (β : k)
    (val : Place k F → k) (bad : Finset k)
    (hUZv : Disjoint U Zv) (hUZa : Disjoint U Za) (hZ : Disjoint Zv Za)
    (ht₀U : t₀ ∉ U) (ht₀v : t₀ ∉ Zv) (ht₀a : t₀ ∉ Za)
    (hcard : Zv.card + 1 ≤ U.card) :
    ∃ g : F,
      g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
      t₀.ord (g - algebraMap k F β) = 1 ∧
      (∀ z ∈ Zv, z.HasValue g (val z)) ∧
      (∀ z ∈ Za, ∃ γ : k, γ ∉ bad ∧ z.HasValue g γ) := by sorry
