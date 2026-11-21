-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_strict_local_resolution
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_strict_local_resolution
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T04:23:32.945699+00:00
-- url     : https://prove2.me/theorems/2441e9f4-b800-4764-8b62-c5c26cc94e63
-- title:
--   Acyclic resolution for strict-local étale cohomology
-- statement:
--   For a proper $f\colon Y\to X$ and a geometric point $s$ of $X$, let $p\colon Y^{sh}\to Y$ be the strict-local projection. Given an injective resolution $I^\bullet$ of an abelian étale sheaf $F$ on $Y$, the cohomology $H^m(Y^{sh},p^{-1}F)$ for $m>0$ equals the homology of the complex $\Gamma(Y^{sh},p^{-1}I^\bullet)$ in degree $m$.
-- source:
--   Stacks Project, Theorem 59.53.1, https://stacks.math.columbia.edu/tag/03Q9.

import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSites

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

open CategoryTheory.Abelian

local instance (W : Scheme.{u}) : (PhilipponEtaleAcyclicCohomology.globalSections W).Additive where
  map_add := rfl

local instance {U V : Scheme.{u}} (g : U ⟶ V) : (PhilipponEtaleSmallSite.pullbackSheaves g).Additive :=
  (PhilipponEtaleSmallSite.pullbackAdjunction g).left_adjoint_additive

theorem AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_strict_local_resolution {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f)).obj F).H (q + 1)) ≅
      (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f) ⋙ PhilipponEtaleAcyclicCohomology.globalSections (pullback (PhilipponEtaleStrictHenselization.toBase s) f)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology (q + 1)) := by sorry
