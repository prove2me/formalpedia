-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_gam_pullUnit
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.gam_pullUnit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:15.09095+00:00
-- url     : https://prove2.me/theorems/2ab18db3-1259-48b5-aaf2-ccff3754d4c6
-- title:
--   Gauge R: gam pull Unit
-- statement:
--   The Gauge R construction uses the gam pull Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqD.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqD.lean#L29-L32

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.gam_pullUnit {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Γ(Sp A, ⊤)ˣ) :
    gam B (pullUnit (spMap f) u : Γ(Sp B, ⊤)) = f (gam A u) := by sorry
