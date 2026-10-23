-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_and_isQuasicoherent_of_isLocallyFreeOfRank
-- name    : AlgebraicGeometry.OModulePresheaf.isCoherent_and_isQuasicoherent_of_isLocallyFreeOfRank
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-22T17:18:28.560419+00:00
-- url     : https://prove2.me/theorems/57eddb3d-a9a5-4077-acac-f43fabfd85c9
-- title:
--   Affine sections and localization of a finite-rank locally free sheaf
-- statement:
--   Let $R$ be a commutative ring, let $X$ be a scheme over $R$, and let $M$ be a locally free sheaf of constant finite rank $d$ on $X$. The presheaf of sections of $M$ has finite modules on affine opens and satisfies localization on every principal affine open.
--
--   For each affine open $U$ and $f\in\Gamma(U,\mathcal O_X)$, the natural map is a localization map:
--
--   $$\Gamma(U,M)_f\simeq\Gamma(D_U(f),M).$$
--
--   In particular, every section over $D_U(f)$ extends to $U$ after multiplication by a sufficiently large power of $f$, and a section on $U$ that restricts to zero is killed by a power of $f$. The module $\Gamma(U,M)$ is finitely generated over $\Gamma(U,\mathcal O_X)$.
--
--   This identifies finite-rank vector bundles with the finiteness and localization interfaces used for coherent-sheaf Euler-characteristic calculations. No Noetherian or field hypothesis is imposed; rank zero and the empty scheme are included.
--
--   **Formalization Note.** The formal conclusion combines the existing sectionwise predicates `IsCoherent` and `IsQuasicoherent`. The former means finite generation on affine opens. The latter records the numerator-extension and power-torsion kernel properties of principal-open restriction maps.
-- source:
--   Consequence of Stacks Project, Section 26.7, especially Lemma 26.7.4 (https://stacks.math.columbia.edu/tag/01I6), and Lemma 10.78.2, equivalences (2), (6), (7) (https://stacks.math.columbia.edu/tag/00NX). A finite-rank locally free sheaf is quasi-coherent. On any affine open it is associated with its module of sections, which is finite projective and hence finitely generated. The principal-open localization comparison in Section 26.7 gives the two displayed formal localization conditions. This is the concrete affine-section consequence in the existing OModulePresheaf interface, rather than a verbatim transcription. No Noetherian assumption is needed.

import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_and_isQuasicoherent_of_isLocallyFreeOfRank
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (d : ℕ) (M : X.Modules) (hM : Scheme.Modules.IsLocallyFreeOfRank d M) :
    (OModulePresheaf.ofModules π M).IsCoherent ∧
      (OModulePresheaf.ofModules π M).IsQuasicoherent := by sorry
