-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent
-- name    : AlgebraicGeometry.Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/07baf182-34bd-5001-93b2-2e777b714ff5
-- title:
--   Sections over an affine open of a tensor product of quasi-coherent modules
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\pi \colon X \to \operatorname{Spec} R$ a morphism of schemes; let $L$ and $M$ be sheaves of $\mathcal O_X$-modules on $X$. Assume that the section data of $L$ and of $M$, regarded via $\pi$ as presheaves of modules over $R$ and over the structure sheaf (with restriction maps the restriction maps of the sheaves), both satisfy the predicate `IsQuasicoherent`: for every affine open $U \subseteq X$ and every $f \in \Gamma(X, U)$, first, every section $x$ over the basic open $X_f \subseteq U$ admits an $n \in \mathbb N$ and a section $y$ over $U$ whose restriction to $X_f$ equals $f^n|_{X_f} \cdot x$, and second, every section $y$ over $U$ restricting to $0$ on $X_f$ is annihilated by $f^n$ for some $n \in \mathbb N$. Then for every affine open $U$ of $X$ the $\Gamma(X,U)$-linear map
--   $$\Gamma(L, U) \otimes_{\Gamma(X,U)} \Gamma(M, U) \longrightarrow \Gamma(L \otimes M, U)$$
--   obtained from the bilinear map `Scheme.Modules.tensorSectionsBilin L M U`, which sends a pair of sections $(s,t)$ to the section of the tensor product sheaf determined by $s \otimes t$, is bijective.
--
--   This is the sections-level form of the standard fact that on an affine scheme the tensor product of the quasi-coherent sheaves attached to two modules is the sheaf attached to the tensor product of those modules. It is used to compare tensor products of sheaves such as $M \otimes L^{\otimes n}$ with tensor products of section modules over the affine opens of a two-chart cover, in the computations of Euler characteristics of alternating Čech complexes and in the resulting finiteness arguments for endomorphisms in the good-reduction Jacobian development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) {L M : X.Modules}
    (hL : (OModulePresheaf.ofModules π L).IsQuasicoherent) (hM : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (U : X.affineOpens) :
    Function.Bijective (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U) :
      Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U)) := by sorry
