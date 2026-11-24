-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvA_psJet_prod_congr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.psJet_prod_congr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:02:16.756259+00:00
-- url     : https://prove2.me/theorems/6498f12a-48d8-4b29-863e-2fb563ee587e
-- title:
--   Harm Inv A: ps Jet prod congr
-- statement:
--   The Harm Inv A construction uses the ps Jet prod congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvA.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvA.lean#L34-L39

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.psJet_prod_congr {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (D : ℕ)
    {f g : κ → MvPowerSeries ι R} (h : ∀ b, psJet D (f b) = psJet D (g b)) :
    psJet D (∏ b, f b) = psJet D (∏ b, g b) := by sorry
