-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_nabVal_eq_const
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.nabVal_eq_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:02:36.887444+00:00
-- url     : https://prove2.me/theorems/293cd10e-ee02-41e5-8541-b516eb589089
-- title:
--   H1: nab Val eq const
-- statement:
--   The H1 construction uses the nab Val eq const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L413-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L413-L419

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj ExpTieAlg NumberField

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.nabVal_eq_const {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB S d O) (h : PS S 2 d) (w0 : O) (k : ℕ) (f : PS S 1 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S)
    (P : MvPolynomial κ S) :
    B.nabVal S h w0 k f u P = constantCoeff (DpolyOf B.G.F u P (f * FB.expS S ((k : S) • B.hL S h w0))) := by sorry
