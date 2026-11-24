-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GlX_tr_E
-- name    : Formalism.CountingSumsFrames.GlX.tr_E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:53.119821+00:00
-- url     : https://prove2.me/theorems/86cb2ebc-8b0a-463c-a56f-5bb047112cca
-- title:
--   Gl X: tr E
-- statement:
--   The Gl X construction uses the tr E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L332-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L332-L338

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.CountingSumsFrames.GlX.tr_E {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) (a b : Fin r)
    (y : LinearMap.range (Lv G h)) (hy : G.E a b y ∈ LinearMap.range (Lv G h)) :
    tr G hk ⟨G.E a b y, hy⟩ = G.E a b (tr G hk y) := by sorry
