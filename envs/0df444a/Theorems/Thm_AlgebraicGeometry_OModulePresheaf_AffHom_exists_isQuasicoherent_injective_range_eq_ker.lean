-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker
-- name    : AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_injective_range_eq_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/1018ac92-6cdf-565f-bfa1-200e5ca3e969
-- title:
--   Affine-local kernel of a morphism of quasi-coherent module data
-- statement:
--   Let $A$ be a commutative ring, $P$ a scheme and $q : P \to \operatorname{Spec} A$ a morphism, and let $G$ and $F$ be `OModulePresheaf` data over $q$: each assigns to every open $U \subseteq P$ a module carrying compatible $A$- and $\Gamma(P,U)$-actions, together with $A$-linear restriction maps that are semilinear for restriction of sections and satisfy the usual identity and composition laws. Assume $G$ and $F$ are quasi-coherent in the sense of `IsQuasicoherent`, i.e. for every affine open $U$ and every $f \in \Gamma(P,U)$ each section over the basic open $P_f$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and every section over $U$ restricting to $0$ on $P_f$ is annihilated by some power of $f$. Let $\theta$ be an `AffHom` from $G$ to $F$, that is a family of $A$-linear maps $\theta_U : G(U) \to F(U)$ indexed by the affine opens $U$, semilinear for the $\Gamma(P,U)$-action and compatible with restriction along inclusions of affine opens. Then there exist module data $K$ over $q$ and an `AffHom` $\iota$ from $K$ to $G$ such that: $K$ is coherent (each $K(U)$ a finite $\Gamma(P,U)$-module for $U$ affine) whenever $P$ is locally Noetherian and $G$ is coherent; $K$ is quasi-coherent; and for every affine open $U$ the map $\iota_U$ is injective with image exactly $\ker \theta_U$.
--
--   This is the existence of the kernel of a morphism of quasi-coherent modules, computed affine-locally, in the setting where the morphism is given only on affine opens. It is used in the construction of kernels inside adic systems of quasi-coherent data, in particular by the results on ranges equal to kernels, on surjectivity of $H^0$ of twisted tensor maps, and on coherent kernels over proper morphisms with adically complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_injective_range_eq_ker
    {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    {G F : OModulePresheaf q} (hGq : G.IsQuasicoherent) (hFq : F.IsQuasicoherent)
    (θ : OModulePresheaf.AffHom G F) :
    ∃ (K : OModulePresheaf q) (ι : OModulePresheaf.AffHom K G),
      (IsLocallyNoetherian P → G.IsCoherent → K.IsCoherent) ∧ K.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Injective (ι.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.range (ι.app U) = LinearMap.ker (θ.app U)) := by sorry
