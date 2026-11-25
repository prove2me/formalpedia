-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_isExpOf_expPhi
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.isExpOf_expPhi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:48.363296+00:00
-- url     : https://prove2.me/theorems/614f8462-7660-4f18-ab6c-f88ba8c0d81d
-- title:
--   H1: is Exp Of exp Phi
-- statement:
--   The H1 construction uses the is Exp Of exp Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L238-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean#L238-L244

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.isExpOf_expPhi {S : Type} [CommRing S] [Algebra ℚ S] {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {d : ℕ} (G : FGLaw S d) (uvec : Lt1 Dw → Fin d → S) (ℓ ε : Pt S 1 d)
    (hℓ1 : dLin ℓ = 1) (hinv : IsInvPair ε ℓ)
    (htr : transF G.F ε ℓ = pt S (n := 2) d 0 + pt S (n := 2) d 1) :
    IsExpOf G.F uvec (ExpOf.expPhi uvec ε) := by sorry
