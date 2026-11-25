-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvA_cc_subst0
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.cc_subst0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:28.725776+00:00
-- url     : https://prove2.me/theorems/6aecb483-33ce-4762-bb5c-9e68305df46c
-- title:
--   Harm Inv A: cc subst0
-- statement:
--   The Harm Inv A construction uses the cc subst0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvA.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvA.lean#L41-L43

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
variable {R : Type} [CommRing R]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.cc_subst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {g : MvPowerSeries σ R}
    (hg : MvPowerSeries.constantCoeff g = 0) : MvPowerSeries.constantCoeff (MvPowerSeries.subst a g) = 0 := by sorry
