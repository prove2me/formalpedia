-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_isPullSec_congr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.isPullSec_congr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:00:16.550797+00:00
-- url     : https://prove2.me/theorems/eeae4755-5fc7-4576-babe-82ee24b718ac
-- title:
--   Exp Tie Germ: is Pull Sec congr
-- statement:
--   The Exp Tie Germ construction uses the is Pull Sec congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieGerm.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieGerm.lean#L115-L120

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
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.isPullSec_congr (a : ℤ) {T T' : Over S0} {h h' : T' ⟶ T} (e : h = h')
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (hs : IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) s s') :
    IsPullSec A L a (h' ▷ A) (whiskerRight_snd _ _) s s' := by sorry
