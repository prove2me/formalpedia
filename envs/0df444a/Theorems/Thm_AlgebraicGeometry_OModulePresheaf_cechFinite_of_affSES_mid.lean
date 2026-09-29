-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_mid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/a6cf7c62-207e-5ef8-aa84-8d144d8f148f
-- title:
--   Čech-finiteness of the middle term of an affine-exact sequence
-- statement:
--   Let $R$ be a commutative Noetherian ring, $V$ a scheme and $\pi \colon V \to \operatorname{Spec} R$ a separated morphism. Let $F_1, F_2, F_3$ be objects of `OModulePresheaf π`, i.e. assignments $U \mapsto F(U)$ on the opens of $V$, each $F(U)$ carrying an $R$-module and a $\Gamma(V,U)$-module structure compatible via the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps $\operatorname{res} \colon F(U') \to F(U)$ for $U \le U'$ that are semilinear for restriction of sections, reflexive and transitive. Let $S$ be an `AffSES F₁ F₂ F₃`: a pair of morphisms $\iota \colon F_1 \to F_2$ and $p \colon F_2 \to F_3$, each given by $\Gamma(V,U)$-semilinear $R$-linear maps on all affine opens $U$ of $V$ commuting with restriction, such that for every affine open $U$ the map $\iota_U$ is injective, $p_U$ is surjective and $\operatorname{range}(\iota_U) = \ker(p_U)$. Let $K$ be an `OrderedAffineCover` of $V$: a finite linearly ordered index type $\iota$ together with affine opens $U_i$ whose supremum is $\top$. Assume `F₁.CechFinite K` and `F₃.CechFinite K`, that is, for $F_1$ and $F_3$ the module $H^0$ of the alternating Čech complex on $K$ and every module $\ker(d^{i+1})/\operatorname{range}(d^{i})$, $i \ge 0$, is a finite $R$-module. Then the same holds for $F_2$: `F₂.CechFinite K`.
--
--   This is the two-out-of-three statement for the middle term in the Čech-cohomological finiteness of a sequence of $\mathcal{O}$-module presheaf data that is exact on affine opens; only the exactness of $H^i(F_1) \to H^i(F_2) \to H^i(F_3)$ is needed, not the connecting maps. It is used in the coherent-finiteness arguments that proceed by reduction along filtrations by powers of an ideal and along integral data, being cited by `cechFinite_of_forall_cechFinite_idealPowQuot`, `cechFinite_of_forall_integral` and `cechFinite_pushforward_of_isIntegral_of_ih`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_mid {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover) (h₁ : F₁.CechFinite K) (h₃ : F₃.CechFinite K) : F₂.CechFinite K := by sorry
