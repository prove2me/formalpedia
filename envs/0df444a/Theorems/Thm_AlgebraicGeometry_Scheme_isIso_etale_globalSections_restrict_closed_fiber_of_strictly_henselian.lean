-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian
-- name    : AlgebraicGeometry.Scheme.isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T18:38:38.880188+00:00
-- url     : https://prove2.me/theorems/49735ac5-1ecf-4b62-a75a-cd679317bcf9
-- title:
--   Proper étale global sections agree with restriction to the closed fiber
-- statement:
--   Let $Y$ be proper over the spectrum of a strictly henselian local ring. For an abelian étale sheaf $F$ on $Y$, restriction from the global sections of $F$ to the global sections of its inverse image on the closed fiber is an isomorphism.
-- source:
--   Stacks Project, Lemma 59.91.3, https://stacks.math.columbia.edu/tag/0A3S.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((PhilipponEtaleAcyclicCohomology.globalSections Y).map
      ((PhilipponEtaleSmallSite.pullbackAdjunction (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f)).unit.app F)) := by sorry
