-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_genPow_scale_pull
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.genPow_scale_pull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:01:20.053383+00:00
-- url     : https://prove2.me/theorems/eb1279c9-cfb5-48b3-9237-66bae064eb48
-- title:
--   Exp Tie Germ: gen Pow scale pull
-- statement:
--   The Exp Tie Germ construction uses the gen Pow scale pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieGerm.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieGerm.lean#L82-L92

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.genPow_scale_pull {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε))
    (h : Z ⟶ Y) (w : Γ(Z, ⊤)ˣ) (k : ℕ) :
    genPow _ _ (scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L φ ε t h)) k =
      scaleGen _ _ (w ^ k) (LB.pullGen Xo.univ.t.PP.L φ _ (genPow φ ε t k) h) := by sorry
