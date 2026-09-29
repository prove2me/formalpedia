-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_opair_oesort_single
-- name    : AlgebraicGeometry.OModulePresheaf.opair_oesort_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/46b83725-4c5d-512a-9232-38263b4edbbb
-- title:
--   Pairing a cochain against the sorted basis element of u
-- statement:
--   Fix a commutative ring $R$, a scheme $V$ and a morphism $\pi : V \to \operatorname{Spec} R$, let $F$ be an `OModulePresheaf` over $\pi$ (an assignment $U \mapsto F.obj\,U$ of $R$-modules, each also a $\Gamma(V,U)$-module compatibly over $R$, together with restriction maps $F.res$ along inclusions of opens, semilinear for the restriction of sections and satisfying the identity and composition laws), and let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $K.\iota$, opens $K.U\,i$ that are affine, with $\bigsqcup_i K.U\,i = \top$. Let $k, n$ be natural numbers, $t : \mathrm{Fin}(k+1) \to K.\iota$ an index tuple, $c$ an ordered $n$-cochain (so $c$ assigns to every tuple $u' : \mathrm{Fin}(n+1) \to K.\iota$ an element of $F.obj(K.ointer\,u')$, where $K.ointer\,u' = \bigwedge_j K.U(u'_j)$), and $u : \mathrm{Fin}(n+1) \to K.\iota$ a tuple with $K.OSub\,u\,t$, i.e. every entry $u_j$ equals some entry $t_i$. The assertion is an equality in $F.obj(K.ointer\,t)$: applying the $\mathbb{Z}$-linear pairing $F.opair\,K\,t\,n\,c$ (which sends a basis tuple $u'$ to $F.res$ of $c\,u'$ to $K.ointer\,t$ when $K.OSub\,u'\,t$ holds, and to $0$ otherwise) to $K.oesort\,n$ of the basis element $\mathrm{single}\,u\,1$ (namely $\operatorname{sign}(\mathrm{sort}\,u)\cdot \mathrm{single}\,(u \circ \mathrm{sort}\,u)\,1$ for injective $u$, and $0$ otherwise) gives the same result as restricting along $K.ointer\,t \le K.ointer\,u$ the value at $u$ of the alternating extension $F.oext\,K\,n$ of the cochain $F.ores\,K\,n\,c$ obtained from $c$ by keeping only its strictly increasing indices.
--
--   This is the compatibility, in the ordered Čech machinery attached to an affine cover, between the pairing of an ordered cochain with signed sorted basis elements of the chain complex and the alternating (sign-twisted) extension of the associated alternating cochain. It is used in the proof of [`AlgebraicGeometry.OModulePresheaf.sub_oext_ores_mem_of_od_eq_zero`](thm.html#AlgebraicGeometry.OModulePresheaf.sub_oext_ores_mem_of_od_eq_zero), part of the comparison of the ordered and alternating Čech complexes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_opair_oesort_single.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.opair_oesort_single
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {k : ℕ} (t : K.OIdx k) (n : ℕ) (c : F.ocochain K n)
    (u : K.OIdx n) (hu : K.OSub u t) :
    F.opair K t n c (K.oesort n (Finsupp.single u 1)) =
      F.res (K.ointer_le_ointer_of_oSub hu) (F.oext K n (F.ores K n c) u) := by sorry
