-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_closed_fiber_of_strictly_henselian
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_closed_fiber_of_strictly_henselian
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-21T02:18:05.58621+00:00
-- url     : https://prove2.me/theorems/ca75b7c8-d407-4810-bde7-678396c99fbd
-- title:
--   Proper étale cohomology comparison with the closed fiber over a strictly henselian local ring
-- statement:
--   Let $R$ be a strictly henselian local ring, and let $Y$ be proper over $\operatorname{Spec} R$. Write $j\colon Y_0\to Y$ for the inclusion of the fiber over the residue field. If an abelian étale sheaf $F$ is killed by a positive integer, then $H^m_{\mathrm{et}}(Y,F)$ and $H^m_{\mathrm{et}}(Y_0,j^{-1}F)$ are isomorphic for every $m>0$. The inverse image $j^{-1}$ is specified by its adjunction to the étale direct image.
-- source:
--   Stacks Project, Theorem 59.91.11, https://stacks.math.columbia.edu/tag/095T.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAbelianDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsSepClosed

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_closed_fiber_of_strictly_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (L : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf (pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f).smallEtaleTopology AddCommGrpCat.{u})
    (adj : L ⊣ PhilipponEtaleClosedPushforward.pushforward (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f))
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (N : ℕ) (hN : N ≠ 0) (htors : N • 𝟙 F = 0) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅
      AddCommGrpCat.of ((L.obj F).H (q + 1))) := by sorry
