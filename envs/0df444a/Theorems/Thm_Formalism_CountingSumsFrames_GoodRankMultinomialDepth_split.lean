-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_split
-- name    : Formalism.CountingSumsFrames.GoodRankMultinomialDepth.split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:33:07.875901+00:00
-- url     : https://prove2.me/theorems/7472e65a-351c-4e0e-8d75-ea9f6ab857f2
-- title:
--   Good Rank Multinomial Depth: split
-- statement:
--   The Good Rank Multinomial Depth construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L136-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L136-L215

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

theorem Formalism.CountingSumsFrames.GoodRankMultinomialDepth.split {B : Type} [AddCommGroup B] [Module O B] {π : O} (hπ : Irreducible π) (E σ : ℕ)
    (g : (Fin σ → O) →ₗ[O] B) :
    ∃ (p : Fin σ → Prop) (j0 : ({k // p k} → O) →ₗ[O] (Fin σ → O))
      (j1 : ({k // ¬ p k} → O) →ₗ[O] (Fin σ → O)),
      (∀ x, ∃ z, g (j0 x) = π ^ (E + 1) • z) ∧
      (∀ x y, j0 x = π • y → ∀ i, π ∣ x i) ∧
      (∀ x z, g (j1 x) = π ^ (E + 1) • z → ∀ i, π ∣ x i) := by sorry
