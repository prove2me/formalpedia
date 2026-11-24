-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_diag_const
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.diag_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:12.290944+00:00
-- url     : https://prove2.me/theorems/2c4efcfc-9286-4b80-99c5-64392abb6c6c
-- title:
--   CInd Fr Fix3: diag const
-- statement:
--   The CInd Fr Fix3 construction uses the diag const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/EvalSinglePointId.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/EvalSinglePointId.lean#L118-L123

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {O : Type} [CommRing O] [StarRing O]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.diag_const (B : FB S d O) (w0 : O) (p : Fin 2) (q : Fin d) :
    MvPowerSeries.constantCoeff ((![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)] : Fin 2 → Pt S 1 d) p q) = 0 := by sorry
