-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.isQuasicoherent_relHPresheaf_chow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/38b5cf6e-0f8b-5e25-9ed3-4ac90262179b
-- title:
--   Quasi-coherence of the relative Čech cohomology presheaf
-- statement:
--   Let $R$ be a commutative ring and let $\pi_Z : Z \to \operatorname{Spec} R$ be a morphism of schemes which is separated. Let $D$ be a Chow datum for $\pi_Z$, that is, data consisting of an integer $N = D.\mathrm{Nd}$, a scheme $V'$, a proper morphism $p = D.p : V' \to Z$, a closed immersion $\iota_N = D.\iota_N : V' \to \operatorname{Proj}$ of the polynomial ring in $N+1$ variables over $R$ with its standard grading, an identification of $\iota_N$ followed by the structure morphism of projective space with $p$ followed by $\pi_Z$, and a dense open $U \subseteq Z$ over which $p$ becomes an isomorphism; and let $b \in \mathbb{N}$. Consider the ordered affine cover `ProjSpace.stdCoverPullback D.ιN` of $V'$ by the preimages $\iota_N^{-1}D_+(X_j)$, $j \in \{0,\dots,N\}$, of the standard basic opens of projective space, and the associated relative Čech presheaf `relHPresheaf`: it assigns to an open $W \subseteq Z$ the $R$-module of alternating $b$-cochains of the cover in the kernel of the Čech differential modulo Čech coboundaries, the cochains being families of sections of $\mathcal{O}_{V'}$ over the sets $\iota_N^{-1}D_+(X_{j_0}) \cap \dots \cap \iota_N^{-1}D_+(X_{j_b}) \cap p^{-1}W$, with restriction maps induced by those of $\mathcal{O}_{V'}$ and with its natural $\Gamma(Z,W)$-module structure. The conclusion is that this presheaf satisfies `IsQuasicoherent`: for every affine open $W \subseteq Z$ and every $f \in \Gamma(Z,W)$, (i) every class $x$ over the basic open $Z_f \subseteq W$ is of the form $\mathrm{res}(y) = f^n \cdot x$ for some $n \in \mathbb{N}$ and some class $y$ over $W$, and (ii) every class $y$ over $W$ whose restriction to $Z_f$ vanishes satisfies $f^n \cdot y = 0$ for some $n \in \mathbb{N}$.
--
--   This is the elementwise form of quasi-coherence of the higher direct images $R^b p_* \mathcal{O}_{V'}$ for the Chow modification $p$, computed by the Čech complex of the pulled-back standard cover of projective space: Čech cohomology commutes with localisation on the base. It feeds the construction of the short exact sequences in [`AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES`](thm.html#AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES) and the inductive finiteness statement [`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.lean

import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.OModulePresheaf.Leray.isQuasicoherent_relHPresheaf_chow {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ] (D : ChowDatumProj πZ) (b : ℕ) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsQuasicoherent := by sorry
