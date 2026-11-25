-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GSR_tan_iff
-- name    : Formalism.L2.Pj.GSR.tan_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:26.75129+00:00
-- url     : https://prove2.me/theorems/e53462f1-97b2-42d1-a1f7-6fe4d3ed1f1a
-- title:
--   GSR: tan iff
-- statement:
--   The GSR construction uses the tan iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecRel.lean#L152-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecRel.lean#L152-L171

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_iff

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
  (hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {k : Type} [CommRing k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)
include hc hg

theorem Formalism.L2.Pj.GSR.tan_iff {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk tk ⟶ G').left ↔ ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := by sorry
