-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range
-- name    : AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_surjective_ker_eq_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/eabab509-f872-5094-bcd4-4690ac5536d6
-- title:
--   Affine-local cokernel of a map of quasi-coherent module data
-- statement:
--   Let $A$ be a commutative ring and let $q : P \to \operatorname{Spec} A$ be a scheme over $A$. An `OModulePresheaf` for $q$ is module data on the open sets of $P$: for every open $U$ an abelian group $F(U)$ carrying an $A$-module structure and a $\Gamma(P,U)$-module structure that are compatible via the $A$-algebra structure on $\Gamma(P,U)$ coming from $q$, together with $A$-linear restriction maps $F(U') \to F(U)$ for $U \le U'$ that are semilinear for restriction of functions and satisfy the identity and composition laws. Such data $F$ is quasi-coherent when for every affine open $U$ and every $f \in \Gamma(P,U)$: each $x \in F(P_f \cap U$-basic open $f)$ satisfies $\mathrm{res}(y) = f^n \cdot x$ for some $n$ and some $y \in F(U)$, and each $y \in F(U)$ restricting to $0$ on the basic open of $f$ is killed by some power of $f$; it is coherent when $F(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$. An `AffHom` $H \to G$ consists of $A$-linear maps $H(U) \to G(U)$ for affine opens $U$ that are $\Gamma(P,U)$-semilinear and commute with restriction between affine opens. Given quasi-coherent $H$ and $G$ and an `AffHom` $h : H \to G$, the theorem asserts the existence of module data $G'$ for $q$ and an `AffHom` $\rho : G \to G'$ such that $G'$ is quasi-coherent, $G'$ is coherent if $G$ is, and for every affine open $U$ of $P$ the map $\rho_U$ is surjective with $\ker \rho_U = \operatorname{im} h_U$.
--
--   This is the cokernel of a morphism of quasi-coherent modules, constructed affine-locally: $G'(U) = \operatorname{coker}(h_U)$ for $U$ affine, in the setting where the morphism is only prescribed on affine opens. It is used in the construction of coherent quotients and of adic systems of modules, being cited by the results producing coimages and cokernels of adic systems and the finiteness statement for kernels of the form $\mathfrak{a}^n \cdot$ top.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_surjective_ker_eq_range
    {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    {H G : OModulePresheaf q} (hHq : H.IsQuasicoherent) (hGq : G.IsQuasicoherent)
    (h : OModulePresheaf.AffHom H G) :
    ∃ (G' : OModulePresheaf q) (ρ : OModulePresheaf.AffHom G G'),
      (G.IsCoherent → G'.IsCoherent) ∧ G'.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Surjective (ρ.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.ker (ρ.app U) = LinearMap.range (h.app U)) := by sorry
