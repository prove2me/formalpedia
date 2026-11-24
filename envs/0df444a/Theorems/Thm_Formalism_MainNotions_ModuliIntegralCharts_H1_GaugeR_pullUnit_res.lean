-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_pullUnit_res
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.pullUnit_res
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:05.248539+00:00
-- url     : https://prove2.me/theorems/af359c1a-9836-4f13-82a6-d8d44ca7bbb9
-- title:
--   Gauge R: pull Unit res
-- statement:
--   The Gauge R construction uses the pull Unit res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqA.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqA.lean#L52-L55

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.pullUnit_res (h : Z ⟶ Y) {V : Y.Opens} {W : Z.Opens} (hWV : W ≤ h ⁻¹ᵁ V) (u : Γ(Y, ⊤)ˣ) :
    res hWV (pullU h V (res (le_top : V ≤ ⊤) u)) = res le_top (pullUnit h u) := by sorry
