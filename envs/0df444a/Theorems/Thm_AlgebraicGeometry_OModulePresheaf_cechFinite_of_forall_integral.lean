-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/327f86ce-6f31-530d-af42-2353d45514d5
-- title:
--   Dévissage driver for Čech finiteness over a proper base
-- statement:
--   Let $R$ be a Noetherian commutative ring, $V$ a scheme and $\pi\colon V\to\operatorname{Spec} R$ a proper morphism, and let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type together with affine opens $U_i\subseteq V$ whose supremum is $\top$. Here an `OModulePresheaf` $\pi$ is the datum of, for each open $U\subseteq V$, an abelian group $F(U)$ carrying an $R$-module structure and a $\Gamma(V,U)$-module structure compatible via the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps along inclusions that are semilinear for restriction of sections and satisfy the usual identities; `CechFinite K` asserts that the zeroth cohomology of the associated Čech complex for $K$ and each $\ker d_{i+1}/\operatorname{im} d_i$ are finite $R$-modules; `IsCoherent` asserts that $F(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$; `IsQuasicoherent` asserts that for every affine open $U$ and every $f\in\Gamma(V,U)$, every section over $V_f$ becomes a restriction from $U$ after multiplication by some power of $f$, and every section over $U$ restricting to $0$ on $V_f$ is annihilated by some power of $f$; and `SupportedIn Y` asserts that $F(U)$ is a subsingleton for every affine open $U$ disjoint from $Y$. Assume: for every closed subset $Z_0\subseteq V$ with nonempty underlying set such that the closed subscheme cut out by the vanishing ideal sheaf data of $Z_0$ is integral, if every coherent quasi-coherent $G$ supported in some closed $Y'<Z_0$ satisfies `CechFinite K`, then the pushforward along the closed immersion of that subscheme of the unit presheaf (the structure sheaf) satisfies `CechFinite K`. Then for every closed $Y\subseteq V$ and every coherent, quasi-coherent $F$ supported in $Y$, $F$ satisfies `CechFinite K`.
--
--   This is the dévissage step in the proof of finiteness of coherent cohomology for a proper morphism over a Noetherian base: it reduces the finiteness of the Čech cohomology of an arbitrary coherent quasi-coherent module datum to the single case of the structure sheaf of an integral closed subscheme. It is used in the derivation of the general finiteness statement [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (K : V.OrderedAffineCover)
    (hInt : ∀ Z₀ : TopologicalSpace.Closeds V, (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
        G.CechFinite K) →
      (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι).CechFinite K) :
    ∀ (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π),
      F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → F.CechFinite K := by sorry
