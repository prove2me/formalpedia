-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_gam_pull
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.gam_pull
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:10.592953+00:00
-- url     : https://prove2.me/theorems/2193e73b-dce7-4504-9539-c84288a9b8ca
-- title:
--   Gauge R: gam pull
-- statement:
--   The Gauge R construction uses the gam pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqD.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqD.lean#L22-L27

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.gam_pull {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Γ(Sp A, ⊤)) :
    gam B (((spMap f).app ⊤).hom x) = f (gam A x) := by sorry
