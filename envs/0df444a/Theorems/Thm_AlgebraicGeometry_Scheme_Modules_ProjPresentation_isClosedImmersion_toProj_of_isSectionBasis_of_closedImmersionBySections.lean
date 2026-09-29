-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/bca01e2e-b291-5692-87a8-2b8e6f98819d
-- title:
--   Presentation by a section basis gives a closed immersion
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} S$ a morphism, and $\mathcal L$ a sheaf of $\mathcal O_X$-modules on $X$. Assume `ClosedImmersionBySections 𝓛 f`: there are an $M$ and a projective presentation $\mathfrak Q$ of $\mathcal L$ along $f$ of size $M$ whose associated morphism $\mathfrak Q.\mathrm{toProj} : X \to \operatorname{Proj}$ of the homogeneous polynomial algebra in $M+1$ variables over $S$ is a closed immersion. Let $\mathfrak P$ be a projective presentation of $\mathcal L$ along $f$ of size $N$, that is: global sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal L, X)$, a morphism $\mathfrak P.\mathrm{toProj} : X \to \mathbb P^N_S$ whose composite with the structure projection to $\operatorname{Spec} S$ is $f$, the framing condition that on every open $V$ contained in the preimage of the basic open $D(X_i)$ the map $g \mapsto g \cdot (\sigma_i|_V)$ from $\Gamma(X,V)$ to $\Gamma(\mathcal L,V)$ is bijective, and the compatibility that on the preimage of $D(X_i)$ the pullback of the ratio $X_j/X_i$ multiplied by $\sigma_i$ equals $\sigma_j$. Assume further `IsSectionBasis f 𝓛 𝔓.σ`, i.e. the $S$-linear map sending $c : \mathrm{Fin}(N+1) \to S$ to $\sum_i f^\sharp(c_i) \cdot \sigma_i \in \Gamma(\mathcal L, X)$ is bijective. Then $\mathfrak P.\mathrm{toProj}$ is a closed immersion.
--
--   This is the statement that if some system of global sections of $\mathcal L$ already embeds $X$ as a closed subscheme of a projective space over $S$, then the presentation attached to a full $S$-basis of $\Gamma(X,\mathcal L)$ — the complete linear system — is likewise a closed immersion. It is used in the construction of projective embeddings of framed polarised abelian schemes, in particular in [`AlgebraicGeometry.Scheme.Modules.exists_projPresentation_sigma_eq_isClosedImmersion_of_isSectionBasis`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_projPresentation_sigma_eq_isClosedImmersion_of_isSectionBasis) and in the fine-moduli and reframing results for framed polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛 : X.Modules}
    (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓛 f N) (hσ : Scheme.Modules.IsSectionBasis f 𝓛 𝔓.σ) :
    IsClosedImmersion 𝔓.toProj := by sorry
