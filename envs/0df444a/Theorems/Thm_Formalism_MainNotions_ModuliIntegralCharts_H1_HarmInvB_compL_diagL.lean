-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvB_compL_diagL
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.compL_diagL
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:17.983842+00:00
-- url     : https://prove2.me/theorems/5e7ff7f4-52fe-43d1-bb8a-f1b057c2a1f2
-- title:
--   Harm Inv B: comp L diag L
-- statement:
--   The Harm Inv B construction uses the comp L diag L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvB.lean#L177-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/HarmInvB.lean#L177-L237

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvB
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB.compL_diagL {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S)
    (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (hinv : IsInvPair ε (fun i => logOf B.G i))
    (a : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (ha : ∀ q, MvPowerSeries.constantCoeff (a q) = 0)
    (hact : ∀ j, MvPowerSeries.subst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) (B.A.act w0 j) =
      MvPowerSeries.subst a (expPhi uvec ε j)) :
    compL (expPhi uvec ε) (diagL B w0 cc) =
      ∑ i, ∑ l, cc i l • (linPt uvec (0 : Fin 1) i * MvPowerSeries.subst a (linPt uvec (0 : Fin 1) l)) := by sorry
