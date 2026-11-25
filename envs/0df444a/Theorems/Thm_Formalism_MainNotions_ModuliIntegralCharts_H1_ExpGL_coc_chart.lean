-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGL_coc_chart
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL.coc_chart
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:32.615603+00:00
-- url     : https://prove2.me/theorems/08a019ea-e7f2-5cca-8883-e955eb9fc165
-- title:
--   Exp GL: coc chart
-- statement:
--   The Exp GL construction uses the coc chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocChart.lean#L76-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocChart.lean#L76-L151

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpSActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BqOriginSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocChart
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
set_option maxHeartbeats 2000000

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGL.coc_chart (hP1 : ExpGJ.PhOneValSt) (hP2 : ExpGJ.PhTwoValSt) (hAd : ExpGJ.AdValSt) (hUid : UnitIdSt)
    (hO : ExpGO.BqOriginSt) (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : IsExpOf C.B.G.F C.uvec φ)
    (hx : IsExpChart y (xExp y C φ))
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j))
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (hu : ∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
      psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))))
    (a : 𝓞 E) (wLa : ExpGC.AdTy Xo a) (hra : ExpGD.AdRel C a wLa) (wLb : ExpGC.AdTy Xo (H.bar a))
    (hrb : ExpGD.AdRel C (H.bar a) wLb) (β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε))
    (hβ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq C.wP a wLa wLb) r z J *
          (val (ExpGC.Bq C.wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
            val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eAt y (xExp y C φ) (ExpGA.eG C φ τ u) m (1 + a * H.bar a))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (xExp y C φ m).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eAt y (xExp y C φ) (ExpGA.eG C φ τ u) m a) 2)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (ExpGA.eG C φ τ u m)
            (eAt y (xExp y C φ) (ExpGA.eG C φ τ u) m (a * H.bar a))))) := by sorry
