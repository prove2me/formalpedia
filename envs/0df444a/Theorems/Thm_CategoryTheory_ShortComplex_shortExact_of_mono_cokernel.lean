-- Prove2me | Theorems.Thm_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel
-- name    : CategoryTheory.ShortComplex.shortExact_of_mono_cokernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/7428ce27-9fed-5158-80d8-8e1b41ec55aa
-- title:
--   A monomorphism and its cokernel form a short exact sequence
-- statement:
--   Let $\mathcal{A}$ be an abelian category (a category with morphism data in a fixed universe, carrying Mathlib's `Abelian` structure), let $X, Y$ be objects of $\mathcal{A}$ and let $f \colon X \to Y$ be a morphism which is a monomorphism. Consider the short complex $0 \to X \xrightarrow{f} Y \xrightarrow{\pi} \operatorname{coker} f \to 0$ formed by $f$, the canonical projection $\pi =$ `cokernel.π f` onto the cokernel of $f$, and the identity $f$ followed by $\pi$ equals zero, which is the defining condition `cokernel.condition f` of the cokernel projection. The assertion is that this short complex is short exact in Mathlib's sense, that is: it is exact at the middle object $Y$, its first map $f$ is a monomorphism, and its second map $\pi$ is an epimorphism.
--
--   This is the elementary fact from homological algebra that every monomorphism in an abelian category sits in a short exact sequence with its cokernel projection. It is used in the construction of the dévissage data for the Néron-core structures attached to the Eisenstein torsion of $J_0(p)$, where an inclusion of abelian fppf sheaves is completed to a short exact sequence by passing to the quotient sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

theorem CategoryTheory.ShortComplex.shortExact_of_mono_cokernel
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {X Y : 𝒜} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact := by sorry
