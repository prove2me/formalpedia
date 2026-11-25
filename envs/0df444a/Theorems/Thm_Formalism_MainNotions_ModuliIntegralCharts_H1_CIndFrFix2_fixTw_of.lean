-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2_fixTw_of
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.fixTw_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:59:30.944004+00:00
-- url     : https://prove2.me/theorems/dd05dbe4-49a6-47ab-a191-ce13137385da
-- title:
--   CInd Fr Fix2: fix Tw of
-- statement:
--   The CInd Fr Fix2 construction uses the fix Tw of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/MulGenScaleRight.lean#L145-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/MulGenScaleRight.lean#L145-L178

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.fixTw_of [StarRing (𝓞 E)] [Algebra ℚ S] (C : ChartAt Xo c y) (T U : ∀ m, (Jet S (Fin 2 × Fin C.d) m)ˣ)
    (hm1 : ∀ m, sub C.d m ![fun j => psIn C.d m ![0, 1] (C.B.G.F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hm2 : ∀ m, sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hs : ∀ m, sub C.d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m)
    (hb : ∀ m a, sub C.d m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] (T m))
    (hstep : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
      (scaleGen _ _ (unitΓ (U m)) (C.e m)))
    (hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m).toMonoidHom
      (T (m + 1)) * U m = T m) (h0 : T 0 = 1) :
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧
      ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ (T m)) (C.e m)) := by sorry
