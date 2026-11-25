-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_sy_ax_of
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.sy_ax_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:50:59.359062+00:00
-- url     : https://prove2.me/theorems/a1b8b16a-df53-5517-bd60-1e405f667993
-- title:
--   FBId Sy: sy ax of
-- statement:
--   The FBId Sy construction uses the sy ax of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdSy.lean#L323-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdSy.lean#L323-L356

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy.sy_ax_of (hL : t.PP.L.IsLB) {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S}
    {sy : MvPowerSeries (Fin 2 × Fin d) S} {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S}
    {e : ∀ m, FrTyG t x0 d x m} (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e)
    (hax : FrAxes t x0 d x e) (b : Bool) :
    ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) sy = 1 := by sorry
