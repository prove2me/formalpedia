-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_exists_betaRaw
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC.exists_betaRaw
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:00:04.145813+00:00
-- url     : https://prove2.me/theorems/27d02b52-d549-4118-a1c7-a56c19f6b6df
-- title:
--   Exp GC: exists beta Raw
-- statement:
--   The Exp GC construction uses the exists beta Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L174-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L174-L198

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC.exists_betaRaw (wP : PrimTy H Xo) (hwP : wP.IsGen) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : AdTy Xo a) (hwa : wLa.IsGen) (wLb : AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (Bq wP a wLa wLb) r z J := by sorry
