-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/7799edd5-f810-57aa-9584-a75c02c93bee
-- title:
--   Čech-finiteness from Čech-finiteness of the graded pieces
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $V$ be a scheme and $\pi\colon V\to\operatorname{Spec} R$ a separated morphism with $V$ locally Noetherian. Let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index set together with affine opens $U_i$ whose supremum is $\top$, let $Y$ be a closed subset of $V$, and let $F$ be an `OModulePresheaf` for $\pi$: an assignment of an $R$-module $F(U)$ to every open $U\subseteq V$, carrying a compatible $\Gamma(V,U)$-module structure (the scalar tower being taken over the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$), with $R$-linear restrictions $F(U')\to F(U)$ for $U\le U'$ that are semilinear for restriction of sections and satisfy the identity and composition laws. Assume: $F$ is coherent, i.e. $F(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$; $F$ is quasi-coherent, i.e. for every affine open $U$ and $f\in\Gamma(V,U)$ each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$; and $F$ is supported in $Y$, i.e. $F(U)$ is a subsingleton whenever the affine open $U$ is disjoint from $Y$. Assume finally that for every $k$ the graded piece `idealPowQuot` of the filtration by the vanishing ideal $I$ of $Y$ — the presheaf $U\mapsto I(U)^kF(U)/I(U)^{k+1}F(U)$ — is Čech-finite for $K$, meaning that $H^0$ and every $H^{i+1}$ of its alternating Čech complex on $K$ is a finite $R$-module. Then $F$ itself is Čech-finite for $K$.
--
--   This is the dévissage step in the proof of the coherence (finiteness) theorem for Čech cohomology on a separated locally Noetherian scheme over a Noetherian base: finiteness for a coherent datum supported in a closed set $Y$ is reduced to finiteness for the successive quotients of the $I_Y$-adic filtration, which are annihilated by $I_Y$. It is used in the Noetherian induction carried out in [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] [IsLocallyNoetherian V] (K : V.OrderedAffineCover) (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) (hStep : ∀ k, (OModulePresheaf.idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F k).CechFinite K) : F.CechFinite K := by sorry
