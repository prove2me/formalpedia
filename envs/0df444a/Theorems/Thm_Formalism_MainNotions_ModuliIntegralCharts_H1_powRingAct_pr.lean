-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_powRingAct_pr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.powRingAct_pr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:02:57.179419+00:00
-- url     : https://prove2.me/theorems/680f10b3-a279-49ca-b77c-a58a03d8651f
-- title:
--   H1: pow Ring Act pr
-- statement:
--   The H1 construction uses the pow Ring Act pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GPowPf.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GPowPf.lean#L71-L73

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GPowSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GPowPf
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A' A : Over S} [GrpObj A'] [GrpObj A] {n : ℕ}
variable [IsCommMonObj A'] [IsCommMonObj A]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.powRingAct_pr (p : IsPowGrp A' A n) {O : Type} [Ring O] (ρ : RingAct A O) (a : O) (i : Fin n) :
    (powRingAct p ρ).act a ≫ p.pr i = p.pr i ≫ ρ.act a := by sorry
