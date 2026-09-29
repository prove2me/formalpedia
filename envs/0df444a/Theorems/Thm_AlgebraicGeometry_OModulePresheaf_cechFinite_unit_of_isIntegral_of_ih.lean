-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/95482fe0-777f-5e19-ab03-ee8f68273b0f
-- title:
--   Finiteness of Čech cohomology of mathcal O_Z for integral proper Z
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $Z$ be a scheme with an integral structure, and let $\pi_Z \colon Z \to \operatorname{Spec} R$ be a proper morphism. Let $K$ be an ordered affine cover of $Z$: a finite linearly ordered index set $\iota$ together with opens $U_i \subseteq Z$, each affine, whose supremum is $\top$. Assume the inductive hypothesis $ih$: for every module presheaf datum $F$ over $\pi_Z$ (an assignment of an $R$-module and $\Gamma(Z,U)$-module $F(U)$ to each open $U$, with compatible $R$-linear restriction maps), if $F$ is coherent, meaning $F(U)$ is a finite $\Gamma(Z,U)$-module for every affine open $U$, and quasi-coherent in the affine-local sense that for every affine open $U$ and every $f \in \Gamma(Z,U)$ each section over the basic open $D(f)$ becomes a restriction after multiplication by some power of $f$ and each section over $U$ dying on $D(f)$ is killed by some power of $f$, and if $F$ is supported in some closed subset $Y' \subsetneq Z$, in the sense that $F(U)$ is trivial for every affine open $U$ disjoint from $Y'$, then $F$ is Čech-finite for $K$, i.e. the degree-zero Čech module and all the modules $\ker d_{i+1}/\operatorname{im} d_i$ of the ordered Čech complex of $F$ with respect to $K$ are finite $R$-modules. Then the unit datum $U \mapsto \Gamma(Z,U)$, with its $R$-algebra structure coming from $\pi_Z$ and the presheaf restrictions, is Čech-finite for $K$.
--
--   This is the integral case of the Noetherian induction (dévissage on the support) which yields the finiteness theorem for the cohomology of a proper morphism over a Noetherian base, EGA III 3.2.1, in the form used in this development for Čech cohomology of ordered affine covers. It is cited by [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper), where the induction is carried out.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih
    {R : Type u} [CommRing R] [IsNoetherianRing R] {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsProper πZ]
    [IsIntegral Z] (K : Z.OrderedAffineCover)
    (ih : ∀ F : OModulePresheaf πZ, F.IsCoherent → F.IsQuasicoherent →
      ∀ Y' < (⊤ : TopologicalSpace.Closeds Z), F.SupportedIn Y' → F.CechFinite K) :
    (OModulePresheaf.unit πZ).CechFinite K := by sorry
