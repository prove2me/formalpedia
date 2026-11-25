-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_scaled_pow
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.scaled_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:17.160569+00:00
-- url     : https://prove2.me/theorems/73f46bef-5058-415c-a5b9-ea0e271efc09
-- title:
--   Gauge R: scaled pow
-- statement:
--   The Gauge R construction uses the scaled pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqA.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqA.lean#L45-L50

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqH
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
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
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {X Y Z : Scheme.{0}} (L : LB X)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.scaled_pow {M : LB Y} (t t' : LB.Gen M) (u : Γ(Y, ⊤)ˣ)
    (h : IsScaled u t t') (k : ℕ) :
    IsScaled (u ^ k) (⟨fun j => t.s j ^ k⟩ : LB.Gen M) ⟨fun j => t'.s j ^ k⟩ := by sorry
