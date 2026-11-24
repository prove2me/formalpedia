-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_atPt_expPhi
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.atPt_expPhi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:00:20.014866+00:00
-- url     : https://prove2.me/theorems/3a14e33f-7fc4-454f-a8be-8fba6aa06c8b
-- title:
--   Exp Of: at Pt exp Phi
-- statement:
--   The Exp Of construction uses the at Pt exp Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L162-L169

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
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.atPt_expPhi (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (b : Fin 2) (i : Fin d) :
    atPt b (expPhi uvec ε i) = subst (fun q : Fin 1 × Fin d => linPt uvec b q.2) (ε i) := by sorry
