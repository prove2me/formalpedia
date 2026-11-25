-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGE_exists_beta
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE.exists_beta
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:47.652908+00:00
-- url     : https://prove2.me/theorems/425a30cc-0496-402b-ae1a-0fa149a12971
-- title:
--   Exp GE: exists beta
-- statement:
--   The Exp GE construction uses the exists beta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ESecToUnit.lean#L33-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ESecToUnit.lean#L33-L82

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ESecToUnit
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE.exists_beta (wP : PrimTy H Xo) (hwP : IsPrim wP) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : ExpGC.AdTy Xo a) (hwa : wLa.IsGen) (wLb : ExpGC.AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
        (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq wP a wLa wLb) r z J *
          (val (ExpGC.Bq wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
            val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹ := by sorry
