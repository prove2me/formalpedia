-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/36a202fd-34e3-5dbe-9329-85582fa75e3a
-- title:
--   Relative Čech cohomology of a Chow datum vanishes over U
-- statement:
--   Let $R$ be a commutative ring, $Z$ a scheme and $\pi_Z : Z \to \operatorname{Spec} R$ a separated morphism, and let $D$ be a `ChowDatumProj` for $\pi_Z$: an integer $N_d$, a scheme $V'$, a proper morphism $p : V' \to Z$, a closed immersion $\iota_N : V' \to \operatorname{Proj}$ of the graded ring of polynomials in $N_d+1$ variables over $R$ with $\iota_N$ followed by the structure map of projective space equal to $p$ followed by $\pi_Z$, together with an open $U \subseteq Z$ whose underlying set is dense and such that the second projection $V' \times_Z U \to U$ is an isomorphism. Let $b \geq 1$. Consider the cover `ProjSpace.stdCoverPullback D.ιN` of $V'$ by the $\iota_N$-preimages of the standard basic opens $D_+(X_j)$, $j \in \mathrm{Fin}(N_d+1)$ (affine opens covering $V'$, with its chosen linear order), and the $\mathcal{O}_Z$-module presheaf datum `relHPresheaf` attached to $p$, $\pi_Z$, this cover and $b$, whose value at an open $W \subseteq Z$ is `relAltH`, the quotient of the kernel of the $b$-th relative alternating Čech differential `relAltd` on the modules $\Gamma(V', \text{(cover intersection)} \cap p^{-1}W)$ by the coboundary submodule `relAltHB`, with restriction maps induced by restriction of sections. The assertion is that this presheaf is `SupportedIn` the closed set complementary to $U$, i.e. for every affine open $W$ of $Z$ whose underlying set is disjoint from $Z \setminus U$ (equivalently $W \subseteq U$), the module at $W$ is a subsingleton, hence zero.
--
--   This is the vanishing of the positive-degree relative Čech cohomology of $\mathcal{O}_{V'}$ along the locus where the Chow modification $p$ is an isomorphism; equivalently, the higher direct images $R^b p_* \mathcal{O}_{V'}$, computed here as Čech cohomology of a fixed finite affine cover, are supported on the closed complement of $U$. It feeds the finiteness argument for Čech cohomology of the structure sheaf in [`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow.lean

import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ] (D : ChowDatumProj πZ) (b : ℕ) (hb : 1 ≤ b) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).SupportedIn
      ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩ := by sorry
