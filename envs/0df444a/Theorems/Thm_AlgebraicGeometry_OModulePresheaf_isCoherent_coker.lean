-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_coker
-- name    : AlgebraicGeometry.OModulePresheaf.isCoherent_coker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/458a0539-fcd3-55d3-b688-0e3c210149e0
-- title:
--   Coherence passes to open-by-open cokernels
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi\colon V\to\operatorname{Spec} R$ a morphism, and let $F,G$ be module-presheaf data over $\pi$: each assigns to every open $U\subseteq V$ an abelian group which is simultaneously an $R$-module and a $\Gamma(V,U)$-module, compatibly with the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps along inclusions $U\le U'$ that are semilinear for the restriction of sections and are functorial. Let $\varphi\colon F\to G$ be a morphism of such data, that is, a family of $R$-linear maps $\varphi_U\colon F(U)\to G(U)$ satisfying $\varphi_U(a\cdot x)=a\cdot\varphi_U(x)$ for $a\in\Gamma(V,U)$ and commuting with the restriction maps. Assume $G$ is coherent in the sense of the project predicate `IsCoherent`: for every affine open $U$ of $V$, the module $G(U)$ is finite over $\Gamma(V,U)$. Then the open-by-open cokernel $\operatorname{coker}\varphi$, whose sections over $U$ are $G(U)/\operatorname{range}\varphi_U$ with the induced $\Gamma(V,U)$-action and the restriction maps induced by those of $G$, is likewise coherent: for every affine open $U$, the quotient $G(U)/\varphi_U(F(U))$ is a finite $\Gamma(V,U)$-module.
--
--   This is one of the closure properties of the open-by-open constructions on module-presheaf data over $\pi$, recording that coherence in the sense of affine-local finite generation is stable under quotients. It is used in the Čech-theoretic finiteness arguments over a two-affine cover, being cited in the construction of the short exact sequences of `Leray.exists_chowSES` and in the statement about Čech pushforwards along proper morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_coker.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_coker {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hG : G.IsCoherent) : (OModulePresheaf.coker φ).IsCoherent := by sorry
