-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartFrameTrA_unit_eq_one_of_eSec
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.unit_eq_one_of_eSec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:58.899971+00:00
-- url     : https://prove2.me/theorems/2cf6399c-4ddd-4f41-a148-4c70fda92ce9
-- title:
--   Chart Frame Tr A: unit eq one of e Sec
-- statement:
--   The Chart Frame Tr A construction uses the unit eq one of e Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartFrameTrA.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartFrameTrA.lean#L58-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.unit_eq_one_of_eSec (hGF : GlobalFnsSt) {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (u : Γ(A.left, ⊤)ˣ) (h : (eSec A).appTop.hom u.val = 1) : u = 1 := by sorry
