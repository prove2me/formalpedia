-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.isCoherent_relHPresheaf_chow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/cdf33748-3b2e-54fd-9133-235112e8e567
-- title:
--   Coherence of relative Čech cohomology for a Chow datum
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $Z$ be a scheme and let $\pi_Z : Z \to \operatorname{Spec} R$ be proper. Let $D$ be a Chow datum for $\pi_Z$, that is: an integer $N = D.Nd$, a scheme $V'$, a morphism $p : V' \to Z$ which is proper, a closed immersion $\iota_N : V' \to \operatorname{Proj}$ of the homogeneous coordinate ring $R[x_0,\dots,x_N]$ with $\iota_N$ followed by the structural projection to $\operatorname{Spec} R$ equal to $p$ followed by $\pi_Z$, together with an open $U \subseteq Z$ whose underlying set is dense and over which $p$ becomes an isomorphism (the second projection of the pullback of $p$ along $U \hookrightarrow Z$ is an isomorphism). Let $b \in \mathbb{N}$, and let $\mathfrak{U}'$ be the ordered affine cover of $V'$ indexed by $\{0,\dots,N\}$ whose $j$-th member is $\iota_N^{-1}D_+(x_j)$. The assertion is that the $\mathcal{O}_Z$-module presheaf datum `relHPresheaf` attached to $p$, $\pi_Z$, $\mathfrak{U}'$ and $b$ — whose value on an open $W \subseteq Z$ is the kernel of the $b$-th differential `relAltd` modulo the submodule of coboundaries `relAltHB`, formed from the alternating Čech groups of the cover $(\mathfrak{U}'_j \cap p^{-1}W)_j$ of $p^{-1}W$ with values in $\mathcal{O}_{V'}$, i.e. the products of the groups $\Gamma(V', \mathfrak{U}'_{\tau} \cap p^{-1}W)$ over multi-indices $\tau$ — is coherent: for every affine open $W \subseteq Z$, this $\Gamma(Z,W)$-module is finitely generated.
--
--   This is the coherence of the higher direct images $R^b p_* \mathcal{O}_{V'}$ of the projective-over-$Z$ morphism underlying a Chow datum, expressed through the alternating Čech complex of the pulled-back standard affine cover of projective space. It feeds the construction of the Chow short exact sequence ([`AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES`](thm.html#AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES)) and the inductive step towards finiteness of Čech cohomology for proper morphisms with integral source ([`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow.lean

import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.OModulePresheaf.Leray.isCoherent_relHPresheaf_chow {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsProper πZ] (D : ChowDatumProj πZ) (b : ℕ) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsCoherent := by sorry
