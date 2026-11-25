-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvA_prod_exp
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.prod_exp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:50:59.752001+00:00
-- url     : https://prove2.me/theorems/aebac55a-c739-4f92-9442-a833d0c31c31
-- title:
--   Harm Inv A: prod exp
-- statement:
--   The Harm Inv A construction uses the prod exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvA.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvA.lean#L52-L59

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.prod_exp {τ : Type} [Algebra ℚ R] : ∀ (n : ℕ) (q : Fin n → MvPowerSeries τ R),
    (∀ b, MvPowerSeries.constantCoeff (q b) = 0) →
    ∏ b, PowerSeries.subst (q b) (PowerSeries.exp R) = PowerSeries.subst (∑ b, q b) (PowerSeries.exp R)
  := by sorry
