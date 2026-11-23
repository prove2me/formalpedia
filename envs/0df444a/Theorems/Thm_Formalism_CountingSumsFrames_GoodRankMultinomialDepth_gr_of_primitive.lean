-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_gr_of_primitive
-- name    : Formalism.CountingSumsFrames.GoodRankMultinomialDepth.gr_of_primitive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:57.26887+00:00
-- url     : https://prove2.me/theorems/eade9159-aca1-46ce-9ceb-bcf1ca3f19ec
-- title:
--   Good Rank Multinomial Depth: gr of primitive
-- statement:
--   The Good Rank Multinomial Depth construction uses the gr of primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L72-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L72-L134

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

theorem Formalism.CountingSumsFrames.GoodRankMultinomialDepth.gr_of_primitive {B ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup B] [Module O B]
    [Module.Free O B] [Module.Finite O B] {π : O} (hπ : Irreducible π) (E : ℕ)
    (h : (ι → O) →ₗ[O] B) (hp : ∀ x z, h x = π ^ (E + 1) • z → ∀ i, π ∣ x i) :
    GR ι π h E := by sorry
