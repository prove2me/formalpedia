-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_closedImmersionBySections_of_forall_isPullback_away
-- name    : AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_forall_isPullback_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/909a009d-1f23-5a0b-8a4b-6a0bb18d473b
-- title:
--   Presentation by sections of an invertible sheaf is local on the base
-- statement:
--   Let $S$ be a commutative ring, let $r : \mathrm{Fin}\,k \to S$ be a finite family whose span is the unit ideal, and for each $i$ let $B_i$ be a localisation of $S$ away from $r_i$. Let $f : A \to \operatorname{Spec} S$ be a morphism of schemes, and for each $i$ let $f'_i : A'_i \to \operatorname{Spec} B_i$ and $g_i : A'_i \to A$ be morphisms making the square with $f$ and $\operatorname{Spec}$ of the structure map $S \to B_i$ cartesian. Assume $f$ is proper, and let $M$ be a module over the structure sheaf of $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the pullback of $M$ along $U \hookrightarrow A$ is isomorphic to the unit module. Let $M'_i$ be modules on $A'_i$ together with isomorphisms $(g_i)^{*}M \cong M'_i$. The hypothesis is that each $M'_i$ satisfies `ClosedImmersionBySections` over $f'_i$, i.e. there are $N_i$ and a `ProjPresentation`: sections $\sigma_0,\dots,\sigma_{N_i}$ of $M'_i$ over $A'_i$ and a morphism $A'_i \to \mathbb{P}^{N_i}_{B_i}$ lifting $f'_i$, such that over any open contained in the preimage of the basic open $D(X_j)$ multiplication by $\sigma_j$ is a bijection from functions to sections of $M'_i$ and the pulled-back ratio $X_l/X_j$ carries $\sigma_j$ to $\sigma_l$, and which is a closed immersion. The conclusion is that $M$ satisfies `ClosedImmersionBySections` over $f$: for some $N$ there is such a presentation of $M$ by $N+1$ global sections whose associated morphism $A \to \mathbb{P}^N_S$ is a closed immersion.
--
--   This is the statement that very ampleness in the naive sense — an invertible sheaf presenting a closed immersion into projective space by finitely many global sections — descends from a finite cover of the base by localisations away from a unit-ideal family, for a proper morphism. It is used in the construction of pullbacks of polarised abelian schemes, where a polarisation known to be presented by sections locally on the base must be so presented globally.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_closedImmersionBySections_of_forall_isPullback_away.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_forall_isPullback_away
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hf : IsProper f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : ∀ i, (A' i).Modules) (e : ∀ i, (Scheme.Modules.pullback (g i)).obj M ≅ M' i)
    (h : ∀ i, Scheme.Modules.ClosedImmersionBySections (M' i) (f' i)) :
    Scheme.Modules.ClosedImmersionBySections M f := by sorry
