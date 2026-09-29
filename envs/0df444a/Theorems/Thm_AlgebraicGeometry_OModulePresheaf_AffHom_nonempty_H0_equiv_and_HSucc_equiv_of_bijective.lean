-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
-- name    : AlgebraicGeometry.OModulePresheaf.AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/910453dc-1ff2-5f64-acaa-16cc1540c052
-- title:
--   Affine-locally bijective morphisms induce Čech cohomology isomorphisms
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a separated morphism. Let $F$ and $G$ be two pieces of $\mathcal{O}$-module presheaf data over $\pi$: each assigns to every open $U \subseteq V$ an $R$-module which is also a $\Gamma(V,U)$-module compatibly (the $R$-action factoring through the algebra structure induced by $\pi$), together with $R$-linear restriction maps along inclusions $U \le U'$ that are semilinear for the restriction of sections and satisfy the identity and composition laws. Let $\varphi$ be an `AffHom` from $F$ to $G$, that is, a family of $R$-linear maps $\varphi_U : F(U) \to G(U)$ indexed by the affine opens $U$ of $V$, commuting with the $\Gamma(V,U)$-action and with restriction along inclusions of affine opens, and assume $\varphi_U$ is bijective for every affine open $U$. Let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $\iota$ together with opens $U_i$, each affine, whose supremum is $\top$. Then there exists an $R$-linear isomorphism $F.H0\,K \cong G.H0\,K$, and for every $i \in \mathbb{N}$ there exists an $R$-linear isomorphism between $F.HSucc\,K\,i$ and $G.HSucc\,K\,i$, the latter being $\ker (d^{i+1}) / \mathrm{im}(d^{i})$ for the alternating Čech complex attached to $K$. The conclusion asserts nonemptiness of the types of such isomorphisms rather than exhibiting a canonical one.
--
--   This is the standard comparison statement that a morphism of module data which is bijective on all affine opens induces isomorphisms on Čech cohomology with respect to a fixed ordered affine cover, in degree $0$ and in all higher degrees. It is used to transport cohomological invariants (ranks, Euler characteristics) between module data that are only known to agree affine-locally, for instance between twists of a presheaf by line bundle powers; eleven results in the Euler-characteristic development cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
    {F G : OModulePresheaf π} (φ : OModulePresheaf.AffHom F G)
    (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U)) (K : V.OrderedAffineCover) :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K) ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K i) := by sorry
