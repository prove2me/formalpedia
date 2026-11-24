-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpActPf_coeff_single_subst
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.coeff_single_subst
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:58:41.460806+00:00
-- url     : https://prove2.me/theorems/4af7a73c-2f8c-4d26-989f-392bb4d730dc
-- title:
--   Exp Act Pf: coeff single subst
-- statement:
--   The Exp Act Pf construction uses the coeff single subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpActPf.lean#L37-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpActPf.lean#L37-L64

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpAct
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpActPf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ExpTieAlg
variable {S : Type} [CommRing S]
open Formalism.FG.SolveVAux

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.coeff_single_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (a : σ → MvPowerSeries τ S) (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ S) (t : τ) :
    coeff (Finsupp.single t 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single t 1) (a s) := by sorry
