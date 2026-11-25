-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2_isFrame_tw
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.isFrame_tw
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:58:34.036796+00:00
-- url     : https://prove2.me/theorems/b2885436-affc-44b8-a0b0-0ebe7de430cd
-- title:
--   CInd Fr Fix2: is Frame tw
-- statement:
--   The CInd Fr Fix2 construction uses the is Frame tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/MulGenScaleRight.lean#L62-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/MulGenScaleRight.lean#L62-L107

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_sub

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MvPolynomial (X)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.isFrame_tw [StarRing (𝓞 E)] {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
    {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hF : IsFrame y d x F act ph1 ph2 sy ad e)
    (hm1 : ∀ m, sub d m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hm2 : ∀ m, sub d m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hs : ∀ m, sub d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m)
    (hb : ∀ m a, sub d m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] (T m)) :
    IsFrame y d x F act ph1 ph2 sy ad (tw y d x e T) := by sorry
