-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_cprod_kill
-- name    : Formalism.CountingSumsFrames.TO.GlX.cprod_kill
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:44.789029+00:00
-- url     : https://prove2.me/theorems/31dc28f6-ba14-4cc0-8872-3fdc92f75e32
-- title:
--   Gl X: cprod kill
-- statement:
--   The Gl X construction uses the cprod kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L47-L52

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.CountingSumsFrames.TO.GlX.cprod_kill {x : V} {e : ℤ} (hx : G.Cas x = ((e : ℤ) : K) • x) (cs : List ℤ) (he : e ∈ cs) :
    G.cprod cs x = 0 := by sorry
