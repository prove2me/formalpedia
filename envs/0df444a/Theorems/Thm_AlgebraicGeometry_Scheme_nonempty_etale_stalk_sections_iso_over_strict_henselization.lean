-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_stalk_sections_iso_over_strict_henselization
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_stalk_sections_iso_over_strict_henselization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T04:23:30.355666+00:00
-- url     : https://prove2.me/theorems/aef9d195-74d4-4545-bc3e-2e947d162183
-- title:
--   Étale direct-image stalk and sections over the strict henselization
-- statement:
--   For a proper morphism $f\colon Y\to X$ and a geometric point $s$ of $X$, the stalk of $f_*F$ at $s$ is naturally isomorphic to the group of sections of the inverse image of $F$ on $Y^{sh}=Y\times_X\operatorname{Spec}\mathcal O^{sh}_{X,s}$.
-- source:
--   Stacks Project, Theorem 59.53.1, https://stacks.math.columbia.edu/tag/03Q9.

import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSites

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_stalk_sections_iso_over_strict_henselization {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) :
    Nonempty (PhilipponEtaleClosedPushforward.pushforward f ⋙ (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u}) ≅
      PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f) ⋙ PhilipponEtaleAcyclicCohomology.globalSections (pullback (PhilipponEtaleStrictHenselization.toBase s) f)) := by sorry
