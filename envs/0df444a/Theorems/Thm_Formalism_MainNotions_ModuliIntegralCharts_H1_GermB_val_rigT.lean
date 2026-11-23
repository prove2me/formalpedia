-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_rigT
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.val_rigT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:58.817985+00:00
-- url     : https://prove2.me/theorems/5adffbd1-0d73-4a01-9846-2f534b926053
-- title:
--   Germ B: val rig T
-- statement:
--   The Germ B construction uses the val rig T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBPrim.lean#L104-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBPrim.lean#L104-L111

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.val_rigT {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (rig : LB.Gen (L.pull (eSec A)))
    (T : Over S0) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (hJ : Good L z J) :
    val (rigT A L rig T 1) r z J = val rig (r ≫ T.hom) z J := by sorry
