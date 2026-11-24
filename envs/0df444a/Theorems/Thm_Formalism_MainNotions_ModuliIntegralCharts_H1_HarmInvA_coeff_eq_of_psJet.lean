-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvA_coeff_eq_of_psJet
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.coeff_eq_of_psJet
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:02:52.294065+00:00
-- url     : https://prove2.me/theorems/f0922b93-8aae-462d-ada7-20a02a57ae13
-- title:
--   Harm Inv A: coeff eq of ps Jet
-- statement:
--   The Harm Inv A construction uses the coeff eq of ps Jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvA.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvA.lean#L14-L22

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.coeff_eq_of_psJet {ι : Type} [Fintype ι] [DecidableEq ι] {D : ℕ} {a b : MvPowerSeries ι R}
    (h : psJet D a = psJet D b) {e : ι →₀ ℕ} (he : e.degree ≤ D) :
    MvPowerSeries.coeff e a = MvPowerSeries.coeff e b := by sorry
