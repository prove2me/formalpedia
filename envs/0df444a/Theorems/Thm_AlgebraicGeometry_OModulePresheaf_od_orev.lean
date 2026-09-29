-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_od_orev
-- name    : AlgebraicGeometry.OModulePresheaf.od_orev
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/5cd91a14-0a9a-5ac1-941f-d24185545d53
-- title:
--   Reversal commutes with the ordered Čech differential
-- statement:
--   Fix a commutative ring $R$ of universe $u$, a scheme $V$ and a morphism $\pi : V \to \operatorname{Spec} R$. Let $F$ be an `OModulePresheaf` for $\pi$: an assignment $U \mapsto F.\mathrm{obj}\,U$ of an $R$-module to each open of $V$, each also a module over $\Gamma(V,U)$ compatibly with $R$ via the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps $F.\mathrm{res}$ for $U \le U'$ that are semilinear for the presheaf restriction on sections and satisfy the identity and composition laws. Let $K$ be an ordered affine cover of $V$, i.e. a finite linearly ordered index type $\iota$ together with opens $K.U\,i$, each affine, whose supremum is $\top$. Let $n$ be a natural number and let $c$ be an ordered $n$-cochain, i.e. a family assigning to each $t : \mathrm{Fin}(n+1) \to \iota$ an element of $F.\mathrm{obj}(\bigsqcap_j K.U(t\,j))$. The conclusion is that the ordered Čech differential `od` and the reversal operator `orev` commute: $\mathrm{od}_{n+1}(\mathrm{orev}_n c) = \mathrm{orev}_{n+1}(\mathrm{od}_n c)$, where $\mathrm{orev}$ in degree $m$ is the $R$-linear map sending $c$ to the cochain whose value at $t$ is $(-1)^{m(m+1)/2}$ times the restriction of $c(t \circ \mathrm{Fin.rev})$ to $\bigsqcap_j K.U(t\,j)$.
--
--   This is the Čech-cochain transposition of the statement that the order-reversing operator $\rho$ is a chain map, the combinatorial input to graded commutativity of the cup product. It is used in the proof of `cls_mul_comm_graded`, the graded-commutativity statement for the product on ordered Čech classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_od_orev.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechReversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.od_orev
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (c : F.ocochain K n) :
    F.od K n (F.orev K n c) = F.orev K (n + 1) (F.od K n c) := by sorry
