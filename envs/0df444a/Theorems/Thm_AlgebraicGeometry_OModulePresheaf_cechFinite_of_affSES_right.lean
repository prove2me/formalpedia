-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/d1396b74-3e43-547c-b5c0-cc72d0a34f5d
-- title:
--   Čech finiteness passes to the quotient in an affine short exact sequence
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $V$ be a scheme and let $\pi \colon V \to \operatorname{Spec} R$ be a separated morphism. Let $F_1, F_2, F_3$ be objects of `OModulePresheaf π`, i.e. data assigning to every open $U \subseteq V$ a type $F.obj\,U$ carrying compatible structures of $R$-module and of $\Gamma(V,U)$-module (the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$), together with $R$-linear restriction maps $F.res \colon F.obj\,U' \to F.obj\,U$ for $U \le U'$ that are semilinear for restriction of sections, reflexive and transitive. Let $S$ be an `AffSES F₁ F₂ F₃`: a pair of maps $\iota \colon F_1 \to F_2$ and $p \colon F_2 \to F_3$, each given by $R$-linear maps on sections over affine opens which are $\Gamma(V,U)$-semilinear and commute with restriction, such that for every affine open $U$ the map $\iota_U$ is injective, $p_U$ is surjective and $\operatorname{range}(\iota_U) = \ker(p_U)$. Let $K$ be an `OrderedAffineCover` of $V$: a finite linearly ordered index set $\iota$ together with affine opens $U_i$ whose supremum is $\top$. Assume `F₁.CechFinite K` and `F₂.CechFinite K`, that is, for $j = 1, 2$ the $R$-module $F_j.H0\,K$ is finite and so is each $F_j.HSucc\,K\,i = \ker(d^{i+1}) / \operatorname{range}(d^{i})$ for all $i$, the differentials being those of the alternating Čech complex of $F_j$ on $K$. Then `F₃.CechFinite K` holds: $F_3.H0\,K$ and all $F_3.HSucc\,K\,i$ are finite $R$-modules.
--
--   This is the two-out-of-three property of Čech finiteness for the right-hand term of a short exact sequence of $\mathcal{O}$-module presheaf data, the standard consequence of the long exact cohomology sequence. It is used in the finiteness arguments for coherent cohomology, namely in the reduction to quotients by powers of an ideal and in the induction for pushforwards along integral morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_right {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover) (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) : F₃.CechFinite K := by sorry
