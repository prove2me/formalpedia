-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_hom_app_eq_of_affHom_ofModules
-- name    : AlgebraicGeometry.OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/d745676a-9658-526a-bbe7-fd8f0443504b
-- title:
--   Morphisms of 𝒪_X-modules from data on affine opens
-- statement:
--   Let $R$ be a commutative ring, let $X$ be a scheme, let $f \colon X \to \operatorname{Spec} R$ be a morphism, and let $M$ and $N$ be sheaves of $\mathcal{O}_X$-modules on $X$. Write $\mathrm{ofModules}\ f\ M$ for the presheaf-of-modules datum whose value on an open $U$ is $\Gamma(M,U)$, regarded both as a $\Gamma(X,U)$-module and as an $R$-module through the algebra map $R \to \Gamma(X,U)$ obtained from $f$ (the inverse of the global-sections isomorphism of $\operatorname{Spec} R$ followed by $f$ on sections from $\top$ to $U$), with restriction maps those of $M$; likewise for $N$. The hypothesis $\Phi$ is an `AffHom` between these data: a family of $R$-linear maps $\Phi_U \colon \Gamma(M,U) \to \Gamma(N,U)$ indexed by the affine opens $U$ of $X$, satisfying $\Phi_U(a \cdot x) = a \cdot \Phi_U(x)$ for $a \in \Gamma(X,U)$, and compatible with restriction in the sense that for affine opens $U \le U'$ the restriction to $U$ followed by $\Phi_U$ agrees with $\Phi_{U'}$ followed by restriction. The conclusion is that there exists a unique morphism $\alpha \colon M \to N$ of $\mathcal{O}_X$-modules whose component on every affine open $U$ agrees with $\Phi_U$ on every section $s \in \Gamma(M,U)$.
--
--   This is the standard statement that a morphism of $\mathcal{O}_X$-modules is determined by, and may be built from, restriction-compatible linear maps on the sections over a basis of opens, here the basis of affine opens (EGA $0_{\mathrm{I}}$ 3.2). It is used to produce morphisms, and hence isomorphisms, of $\mathcal{O}_X$-modules from compatible affine-local data, as in the construction of isomorphisms of invertible modules from compatible isomorphisms over adic thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_hom_app_eq_of_affHom_ofModules.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M N : X.Modules)
    (Φ : OModulePresheaf.AffHom (OModulePresheaf.ofModules f M) (OModulePresheaf.ofModules f N)) :
    ∃! α : M ⟶ N, ∀ (U : X.affineOpens) (s : Γ(M, U.1)), α.app U.1 s = Φ.app U s := by sorry
