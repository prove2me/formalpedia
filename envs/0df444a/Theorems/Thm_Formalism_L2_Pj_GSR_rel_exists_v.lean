-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GSR_rel_exists_v
-- name    : Formalism.L2.Pj.GSR.rel_exists_v
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:56:34.596952+00:00
-- url     : https://prove2.me/theorems/aa8ca628-e3dc-467e-b57e-e5c3d02ad611
-- title:
--   GSR: rel exists v
-- statement:
--   The GSR construction uses the rel exists v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecRel.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecRel.lean#L70-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_v

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GSR
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [CommRing k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)
variable {tk g}
include hc hg

theorem Formalism.L2.Pj.GSR.rel_exists_v {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') :
    ∃ v : X ⟶ (Over.pullback g).obj G, Rel (F := F) tk g w v := by sorry
