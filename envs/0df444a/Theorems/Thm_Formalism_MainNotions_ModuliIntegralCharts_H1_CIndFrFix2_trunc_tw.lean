-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2_trunc_tw
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.trunc_tw
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:58:22.054161+00:00
-- url     : https://prove2.me/theorems/2db147bf-a8f4-4508-b13b-bf859bba215a
-- title:
--   CInd Fr Fix2: trunc tw
-- statement:
--   The CInd Fr Fix2 construction uses the trunc tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/MulGenScaleRight.lean#L109-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/MulGenScaleRight.lean#L109-L136

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.trunc_tw (e : ∀ m, FrTy y d x m) (T U : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hstep : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (e (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (scaleGen _ _ (unitΓ (U m)) (e m)))
    (hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1)) * U m = T m) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (tw y d x e T (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (tw y d x e T m) := by sorry
