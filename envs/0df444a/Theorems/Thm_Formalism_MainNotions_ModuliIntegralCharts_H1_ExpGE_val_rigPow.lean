-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGE_val_rigPow
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE.val_rigPow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:59:54.621807+00:00
-- url     : https://prove2.me/theorems/af6f404b-d340-49c2-a94a-fc200d9e9125
-- title:
--   Exp GE: val rig Pow
-- statement:
--   The Exp GE construction uses the val rig Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ESecToUnit.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ESecToUnit.lean#L17-L21

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ESecToUnit
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE.val_rigPow {Z : Scheme.{0}} (k : ℤ) (r : Z ⟶ (𝟙_ (Over Xo.X)).left) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) :
    val (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig k) r z J = val Xo.univ.t.PP.rig r z J ^ k := by sorry
