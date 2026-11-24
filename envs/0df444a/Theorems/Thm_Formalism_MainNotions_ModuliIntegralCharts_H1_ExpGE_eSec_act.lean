-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGE_eSec_act
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE.eSec_act
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:17.584859+00:00
-- url     : https://prove2.me/theorems/e2518e4b-439e-41dd-84a3-1509a815ac95
-- title:
--   Exp GE: e Sec act
-- statement:
--   The Exp GE construction uses the e Sec act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ESecToUnit.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ESecToUnit.lean#L23-L26

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE.eSec_act (c : 𝓞 E) : eSec Xo.univ.t.G ≫ (Xo.univ.t.act.act c).left = eSec Xo.univ.t.G := by sorry
