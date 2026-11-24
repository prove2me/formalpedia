-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_value_scaled
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.value_scaled
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:10.301798+00:00
-- url     : https://prove2.me/theorems/5f06ee16-fb67-4f3a-af3b-b6225968520b
-- title:
--   Gauge R: value scaled
-- statement:
--   The Gauge R construction uses the value scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqD.lean#L45-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqD.lean#L45-L75

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeBeta
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqD
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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.value_scaled {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (a : ℤ)
    {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ τ' : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)))
    (v v' : Γ(T.left, ⊤)) (U : Γ(T.left, ⊤)ˣ) (h : IsValueAt A L a s z τ v) (h' : IsValueAt A L a s z τ' v')
    (hs : IsScaled U τ τ') : v = (U : Γ(T.left, ⊤)) * v' := by sorry
