-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_gr_comp
-- name    : Formalism.CountingSumsFrames.GoodRankMultinomialDepth.gr_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:54.003675+00:00
-- url     : https://prove2.me/theorems/05f14e77-5da3-4ab7-8861-93655478fef7
-- title:
--   Good Rank Multinomial Depth: gr comp
-- statement:
--   The Good Rank Multinomial Depth construction uses the gr comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L18-L22

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

theorem Formalism.CountingSumsFrames.GoodRankMultinomialDepth.gr_comp {A A' B ι : Type} [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O A']
    [AddCommGroup B] [Module O B] {π : O} {f : A →ₗ[O] B} {D : ℕ} (w : A' →ₗ[O] A)
    (h : GR ι π (f ∘ₗ w) D) : GR ι π f D := by sorry
