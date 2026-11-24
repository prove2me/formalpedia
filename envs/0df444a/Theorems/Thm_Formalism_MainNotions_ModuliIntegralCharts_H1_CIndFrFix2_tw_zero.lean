-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2_tw_zero
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.tw_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:58:30.914532+00:00
-- url     : https://prove2.me/theorems/1f56c7e8-fcc2-44cf-9a8f-28d825121157
-- title:
--   CInd Fr Fix2: tw zero
-- statement:
--   The CInd Fr Fix2 construction uses the tw zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/MulGenScaleRight.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/MulGenScaleRight.lean#L45-L51

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.tw_zero (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (h0 : T 0 = 1) :
    tw y d x e T 0 = e 0 := by sorry
