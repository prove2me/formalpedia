-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_pow_succ_dvd_of_not_dvd
-- name    : Formalism.CountingSumsFrames.GoodRankMultinomialDepth.pow_succ_dvd_of_not_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:33:03.586796+00:00
-- url     : https://prove2.me/theorems/cce91727-1c2d-4e05-9fa3-8696fc57d733
-- title:
--   Good Rank Multinomial Depth: pow succ dvd of not dvd
-- statement:
--   The Good Rank Multinomial Depth construction uses the pow succ dvd of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/LemmaS.lean#L57-L70

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

theorem Formalism.CountingSumsFrames.GoodRankMultinomialDepth.pow_succ_dvd_of_not_dvd {π : O} (hπ : Irreducible π) {a : O} {E : ℕ}
    (h : ¬ a ∣ π ^ E) : π ^ (E + 1) ∣ a := by sorry
