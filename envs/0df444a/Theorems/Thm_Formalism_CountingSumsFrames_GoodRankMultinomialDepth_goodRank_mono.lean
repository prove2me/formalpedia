-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_goodRank_mono
-- name    : Formalism.CountingSumsFrames.GoodRankMultinomialDepth.goodRank_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:33:02.715814+00:00
-- url     : https://prove2.me/theorems/ecdc4960-0184-4d23-8a5c-86907206e7f7
-- title:
--   Good Rank Multinomial Depth: good Rank mono
-- statement:
--   The Good Rank Multinomial Depth construction uses the good Rank mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L38-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L38-L55

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.GoodRankMultinomialDepth
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.CountingSumsFrames.GoodRankMultinomialDepth.goodRank_mono {A B : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    {π : O} {f : A →ₗ[O] B} {n m D : ℕ} (h : Formalism.G0.GoodRank π f n D) (hmn : m ≤ n) :
    Formalism.G0.GoodRank π f m D := by sorry
