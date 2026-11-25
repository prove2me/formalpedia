-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GSR_rel_act
-- name    : Formalism.L2.Pj.GSR.rel_act
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:55.464678+00:00
-- url     : https://prove2.me/theorems/ff488d90-5f0e-49c7-b300-73c501483542
-- title:
--   GSR: rel act
-- statement:
--   The GSR construction uses the rel act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecRel.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecRel.lean#L125-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_act

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

theorem Formalism.L2.Pj.GSR.rel_act (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) {X : Over (Spec (CommRingCat.of k))}
    {w : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) :
    Rel (F := F) tk g (w ≫ a) (v ≫ (Over.pullback g).map b) := by sorry
