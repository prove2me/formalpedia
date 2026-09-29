-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_unit
-- name    : AlgebraicGeometry.OModulePresheaf.isQuasicoherent_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4f07d577-e40c-5d8e-9479-142f913c9535
-- title:
--   Quasi-coherence of the structure-sheaf module presheaf
-- statement:
--   Let $R$ be a commutative ring, let $V$ be a scheme, and let $\pi \colon V \to \operatorname{Spec} R$ be a morphism of schemes. Consider the module presheaf `OModulePresheaf.unit π` over $\pi$: it assigns to each open $U \subseteq V$ the ring $\Gamma(V, U)$, regarded as an $R$-module through the $R$-algebra structure $R \to \Gamma(V,U)$ induced by $\pi$ (the composite of the inverse of the global-sections isomorphism of $\operatorname{Spec} R$ with $\pi$ on sections over $U$) and as a module over itself, with restriction maps given by the restriction homomorphisms of the structure sheaf. The theorem asserts that this datum satisfies `IsQuasicoherent`, that is: for every affine open $U$ of $V$ and every $f \in \Gamma(V, U)$, first, for each $x \in \Gamma(V, V.basicOpen\,f)$ there are $n \in \mathbb{N}$ and $y \in \Gamma(V, U)$ with $y|_{D(f)} = (f^n)|_{D(f)} \cdot x$; and second, every $y \in \Gamma(V,U)$ with $y|_{D(f)} = 0$ satisfies $f^n y = 0$ for some $n \in \mathbb{N}$. No hypothesis on $V$ or on $\pi$ beyond their existence is required.
--
--   This is the quasi-coherence of the structure sheaf $\mathcal{O}_V$, expressed in the elementary form that on an affine open $U$ the sections over a basic open $D(f)$ are obtained from $\Gamma(V,U)$ by inverting $f$, packaged so that it feeds the Čech machinery for module presheaves. It is used in the proof that a Čech $1$-cocycle condition forces membership in the image of the degree-zero differential for the structure sheaf on affine schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_unit
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) :
    (OModulePresheaf.unit π).IsQuasicoherent := by sorry
