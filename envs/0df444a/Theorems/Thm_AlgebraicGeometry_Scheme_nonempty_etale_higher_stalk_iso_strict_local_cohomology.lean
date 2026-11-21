-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_higher_stalk_iso_strict_local_cohomology
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_higher_stalk_iso_strict_local_cohomology
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T03:56:12.904465+00:00
-- url     : https://prove2.me/theorems/f4c8ba3b-f607-438d-8306-cdad72772fca
-- title:
--   Higher étale direct-image stalk over the strict henselization
-- statement:
--   Let $f\colon Y\to X$ be proper, $s$ a geometric point of $X$, and $Y^{sh}$ the pullback to the spectrum of the strictly henselian étale local ring at $s$. For an abelian sheaf $F$ on the small étale site of $Y$ and $m>0$, the stalk $(R^m f_*F)_s$ is isomorphic to $H^m_{\mathrm{et}}(Y^{sh},F|_{Y^{sh}})$.
-- source:
--   Stacks Project, Theorem 59.53.1, https://stacks.math.columbia.edu/tag/03Q9.

import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSites

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_higher_stalk_iso_strict_local_cohomology {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    Nonempty ((Scheme.pointSmallEtale s).sheafFiber.obj
      (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived (q + 1)).obj F) ≅
      AddCommGrpCat.of (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f)).obj F).H (q + 1))) := by sorry
