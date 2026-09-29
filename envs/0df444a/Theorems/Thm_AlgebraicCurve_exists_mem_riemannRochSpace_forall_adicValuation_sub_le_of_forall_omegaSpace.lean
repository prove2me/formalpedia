-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace
-- name    : AlgebraicCurve.exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/593dea59-d89c-52ff-ab60-4129e425931a
-- title:
--   Functions in L(D) from orthogonality to Ω(D-E)
-- statement:
--   Let $K \subseteq F$ be fields, $F$ a $K$-algebra, and let the places of $F/K$ be the valuation subrings of $F$ containing $\mathrm{im}(K)$, proper in $F$ and principal ideal rings, each carrying its $\mathbb{Z}^{m0}$-valued adic valuation `Place.adicValuation`. Let $D$ be a divisor, i.e. a finitely supported function from places to $\mathbb{Z}$, let $T$ be a finite set of places, and let $g$ assign to every place an element of $F$ with $x.\mathrm{adicValuation}(g\,x) \le \exp(D\,x)$ for all $x \in T$. Let $r$ be an element of [`AlgebraicCurve.adeleSpace K F`](def/AlgebraicCurve_AdelicIndex.html#L94), the union over all divisors $E$ of the spaces of families $\alpha$ with $v(\alpha_v) \le \exp(E\,v)$ at every $v$, and assume its coordinates satisfy $r_v = g\,v$ for $v \in T$ and $r_v = 0$ for $v \notin T$. Put $E = \sum_{x \in T} \delta_x$ (the sum of the divisors $\mathrm{single}\,x\,1$). Assume finally that every $\mu$ in [`AlgebraicCurve.omegaSpace (D - E)`](def/AlgebraicCurve_AdelicIndex.html#L160), that is every $K$-linear functional on the adele space annihilating both the $(D-E)$-bounded adeles and the diagonal image of $F$, satisfies $\mu(r) = 0$. Then there exists $f$ in [`AlgebraicCurve.riemannRochSpace D`](def/AlgebraicCurve_Repartitions.html#L105), i.e. with $v(f) \le \exp(D\,v)$ at every place $v$, such that $x.\mathrm{adicValuation}(f - g\,x) \le \exp(D\,x - 1)$ for every $x \in T$.
--
--   This is the exactness statement underlying the Riemann–Roch sequence $0 \to L(D-E) \to L(D) \to \bigoplus_{x \in T} \mathfrak{m}_x^{-D(x)}/\mathfrak{m}_x^{-D(x)+1} \to H^1(D-E)$, read in Weil's adelic formulation with $H^1(D-E)^{\vee}$ realised as the space of Weil differentials bounded by $D-E$: an adele supported on $T$ with prescribed principal parts that is killed by all such differentials is realised by a global function in $L(D)$ up to one order of vanishing. It is used in the construction of Hecke-theoretic forms on modular curves, where it is cited in [`ModularCurve.SSHeckeV2.exists_theta_ker_iff_range_resFnFun_and_apply_weilOfKaehler`](thm.html#ModularCurve.SSHeckeV2.exists_theta_ker_iff_range_resFnFun_and_apply_weilOfKaehler).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WithZero

theorem AlgebraicCurve.exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : AlgebraicCurve.Divisor K F) (T : Finset (AlgebraicCurve.Place K F)) (g : AlgebraicCurve.Place K F → F)
    (hg : ∀ x ∈ T, x.adicValuation (g x) ≤ exp (D x))
    (r : ↥(AlgebraicCurve.adeleSpace K F))
    (hrT : ∀ v ∈ T, (r : AlgebraicCurve.Place K F → F) v = g v) (hr0 : ∀ v ∉ T, (r : AlgebraicCurve.Place K F → F) v = 0)
    (horth : ∀ μ ∈ AlgebraicCurve.omegaSpace (K := K) (F := F) (D - ∑ x ∈ T, Finsupp.single x 1), μ r = 0) :
    ∃ f ∈ AlgebraicCurve.riemannRochSpace (K := K) (F := F) D,
      ∀ x ∈ T, x.adicValuation (f - g x) ≤ exp (D x - 1) := by sorry
