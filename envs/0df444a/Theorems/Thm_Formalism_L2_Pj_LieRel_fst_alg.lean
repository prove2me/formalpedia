-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LieRel_fst_alg
-- name    : Formalism.L2.Pj.LieRel.fst_alg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:27.684972+00:00
-- url     : https://prove2.me/theorems/47b596ba-01ae-4960-8793-d2e789405da2
-- title:
--   Lie Rel: fst alg
-- statement:
--   The Lie Rel construction uses the fst alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieRel.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieRel.lean#L125-L130

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieRel
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_list_prod_tan__79ee0da3542e
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_w
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tcoord tmap IsUnivChart tvec_tmap tcoord_spec tvec_inj list_prod_tan' tcoord_scale
  tcoord_tvec isTan_tvec isTan_scale tvec_eig_iff scaleD fB Rel liftT viaT rel_exists_w rel_exists_v rel_eq_iff
  rel_prod rel_pre tan_iff eig_iff one_left' sp JetR)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : Sp K ⟶ S) {G' : Over (Sp K)} [GrpObj G']
  {F1 : G'.left ⟶ A.left} (h1 : IsGrpPullback G' A x F1) {V : Type} [CommRing V] [Algebra V K] {G : Over (Sp V)}
  [GrpObj G] {F2 : G'.left ⟶ G.left} (h2 : IsGrpPullback G' G (fB V K) F2)

theorem Formalism.L2.Pj.LieRel.fst_alg : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) := by sorry
