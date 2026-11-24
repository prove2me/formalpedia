-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_coeff_single_subst
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.coeff_single_subst
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:59:44.202919+00:00
-- url     : https://prove2.me/theorems/d9f66301-5879-4d18-988c-4284b50c57ad
-- title:
--   Exp Of: coeff single subst
-- statement:
--   The Exp Of construction uses the coeff single subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L21-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L21-L48

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
variable {R : Type} [CommRing R]
open Formalism.FG.SolveVAux

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.coeff_single_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (a : σ → MvPowerSeries τ R) (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (t : τ) :
    coeff (Finsupp.single t 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single t 1) (a s) := by sorry
