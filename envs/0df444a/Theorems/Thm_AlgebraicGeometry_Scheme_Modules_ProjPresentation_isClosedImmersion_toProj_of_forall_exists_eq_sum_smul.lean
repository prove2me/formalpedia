-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/bb26d8b9-9683-53ac-8313-0b88c78cfbaa
-- title:
--   Closed immersions transfer to presentations with spanning sections
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} S$ a morphism, and $\mathcal L$ a module over $X$. Let $M, N$ be natural numbers and let $\mathfrak Q$, $\mathfrak P$ be two `ProjPresentation` data for $\mathcal L$ over $f$ of sizes $M$ and $N$: thus $\mathfrak Q$ consists of global sections $\mathfrak Q.\sigma_0,\dots,\mathfrak Q.\sigma_M \in \Gamma(\mathcal L,\top)$ together with a morphism $\mathfrak Q.\mathrm{toProj} : X \to \operatorname{Proj}$ of the ring of polynomials in $N'+1$ variables over $S$ with its standard grading ($N'=M$ here), whose composite with the structural morphism $\pi$ to $\operatorname{Spec} S$ is $f$, such that on every open $V$ of $X$ contained in the preimage of the basic open $D(X_i)$ the map $g \mapsto g \cdot (\mathfrak Q.\sigma_i|_V)$ from $\Gamma(X,V)$ to $\Gamma(\mathcal L,V)$ is bijective, and such that the pullback along $\mathfrak Q.\mathrm{toProj}$ of the ratio $X_j/X_i$ on $D(X_i)$ carries $\mathfrak Q.\sigma_i$ to $\mathfrak Q.\sigma_j$ after restriction to that preimage; similarly for $\mathfrak P$ with $N+1$ sections. Assume that each $\mathfrak Q.\sigma_j$ is an $S$-linear combination $\sum_k a_k \cdot \mathfrak P.\sigma_k$, the scalars $a_k \in S$ acting through $f$ on global sections, and that $\mathfrak Q.\mathrm{toProj}$ is a closed immersion. Then $\mathfrak P.\mathrm{toProj}$ is a closed immersion.
--
--   This is the statement that, if the sections defining one morphism to projective space are $S$-linear combinations of those defining another, then a closed immersion for the first presentation forces one for the second — classically, cancellation of a closed immersion along the linear projection determined by the coefficient matrix. It is used to verify that presentations of $\mathcal L$ by other systems of sections are closed immersions, in particular in the criteria for closed immersions by sections and in the descent of such criteria along faithfully flat pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
    {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛 : X.Modules}
    {M N : ℕ} (𝔔 : Scheme.Modules.ProjPresentation 𝓛 f M) (𝔓 : Scheme.Modules.ProjPresentation 𝓛 f N)
    (hspan : ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → S,
      𝔔.σ j = ∑ k, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (a k))) • 𝔓.σ k)
    (hQ : IsClosedImmersion 𝔔.toProj) :
    IsClosedImmersion 𝔓.toProj := by sorry
