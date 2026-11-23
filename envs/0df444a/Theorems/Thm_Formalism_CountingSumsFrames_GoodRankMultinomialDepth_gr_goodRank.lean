-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_gr_goodRank
-- name    : Formalism.CountingSumsFrames.GoodRankMultinomialDepth.gr_goodRank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:58.646352+00:00
-- url     : https://prove2.me/theorems/214bb895-9783-4dec-866c-bd11438040ac
-- title:
--   Good Rank Multinomial Depth: gr good Rank
-- statement:
--   The Good Rank Multinomial Depth construction uses the gr good Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L24-L36

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

theorem Formalism.CountingSumsFrames.GoodRankMultinomialDepth.gr_goodRank {A B ι : Type} [Fintype ι] [AddCommGroup A] [Module O A] [AddCommGroup B]
    [Module O B] {π : O} {f : A →ₗ[O] B} {D : ℕ} (h : GR ι π f D) :
    Formalism.G0.GoodRank π f (Fintype.card ι) D := by sorry
