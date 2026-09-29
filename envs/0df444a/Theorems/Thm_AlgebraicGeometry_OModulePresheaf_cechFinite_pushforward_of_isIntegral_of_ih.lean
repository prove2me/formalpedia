-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/7bbeb7a9-690c-57f4-b888-a110e8a29a28
-- title:
--   Dévissage step: Čech finiteness along an integral closed subscheme
-- statement:
--   Let $R$ be a Noetherian commutative ring, $V$ a scheme and $\pi\colon V\to\operatorname{Spec} R$ a proper morphism, and let $K$ be an ordered affine cover of $V$, i.e. a finite linearly ordered index set together with affine opens covering $V$. Let $Z_0$ be a closed subset of $V$ with $Z_0\neq\emptyset$, write $j$ for the closed immersion `(Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι` of the subscheme attached to the vanishing ideal sheaf data of $Z_0$, and assume that this subscheme is integral. For an $\mathcal O$-module presheaf $F$ over a structure morphism — an assignment of an $R$-module and $\Gamma(\,\cdot\,)$-module $F(U)$ to each open, with compatible scalars and $R$-linear, semilinear restrictions — call $F$ Čech-finite for $K$ when $F.H0\,K$ and all the quotients $\ker d^{i+1}/\operatorname{im} d^i$ of the alternating Čech complex of $F$ on $K$ are finite $R$-modules. Assume: the pushforward along $j$ of the unit presheaf $U\mapsto\Gamma(\,j^{-1}U)$ is Čech-finite for $K$; and, for every closed $Y'\subsetneq Z_0$, every $\mathcal O$-module presheaf $G$ over $\pi$ that is coherent ($G(U)$ finite over $\Gamma(V,U)$ for all affine opens $U$), quasi-coherent (sections over a basic open $D(f)$ become restrictions after multiplying by a power of $f$, and sections restricting to $0$ on $D(f)$ are killed by a power of $f$) and supported in $Y'$ ($G(U)$ is a subsingleton whenever the affine open $U$ misses $Y'$) is Čech-finite for $K$. Then for every $\mathcal O$-module presheaf $H$ over $j$ followed by $\pi$ whose pushforward $j_*H$ along $j$ is coherent and quasi-coherent, $j_*H$ is Čech-finite for $K$.
--
--   This is the pivotal step of a dévissage argument proving Grothendieck's finiteness theorem for proper morphisms over a Noetherian base, in the concrete form that the alternating Čech cohomology of a coherent quasi-coherent module presheaf on a fixed finite affine cover is finitely generated. It is invoked in the Noetherian induction on closed subsets carried out in [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral), the induction hypothesis for strictly smaller closed subsets and the case of the structure sheaf of the integral subscheme being supplied as hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (K : V.OrderedAffineCover) {Z₀ : TopologicalSpace.Closeds V} (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (hO : (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι).CechFinite K)
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
      G.CechFinite K)
    (H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hc : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsCoherent)
    (hq : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsQuasicoherent) :
    (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).CechFinite K := by sorry
