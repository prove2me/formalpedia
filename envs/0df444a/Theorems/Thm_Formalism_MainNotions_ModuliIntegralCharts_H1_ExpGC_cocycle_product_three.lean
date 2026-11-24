-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_cocycle_product_three
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC.cocycle_product_three
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:58:57.426234+00:00
-- url     : https://prove2.me/theorems/4bfa559c-e12d-45b3-a5c5-e32c03b0c851
-- title:
--   Exp GC: cocycle product three
-- statement:
--   The Exp GC construction uses the cocycle product three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L87-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CocycleProductThree.lean#L87-L123

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
set_option maxHeartbeats 800000

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC.cocycle_product_three {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : thK, h (thφ Xo.univ.t.G xs I) ^ thε I =
      (h (1 : T ⟶ Xo.univ.t.G).left)⁻¹ * h (xs 0 * 1).left * h (xs 1 * 1).left * h (xs 2 * 1).left *
        (h (xs 0 * (xs 1 * 1)).left)⁻¹ * (h (xs 0 * (xs 2 * 1)).left)⁻¹ * (h (xs 1 * (xs 2 * 1)).left)⁻¹ *
          h (xs 0 * (xs 1 * (xs 2 * 1))).left := by sorry
