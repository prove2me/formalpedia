-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_E_Lv
-- name    : Formalism.CountingSumsFrames.TO.GlX.E_Lv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:41.056801+00:00
-- url     : https://prove2.me/theorems/52f37ea8-f397-4db3-a907-a2331959f679
-- title:
--   Gl X: E Lv
-- statement:
--   The Gl X construction uses the E Lv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L285-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L285-L290

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

theorem Formalism.CountingSumsFrames.TO.GlX.E_Lv (v : V) (a b : Fin r) (c : List (Fin r × Fin r) →₀ K) :
    G.E a b (Lv G v c) = Lv G v (Finsupp.mapDomain (List.cons (a, b)) c) := by sorry
