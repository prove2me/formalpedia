-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_finrank_har
-- name    : Formalism.CountingSumsFrames.Har2.finrank_har
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:47.987715+00:00
-- url     : https://prove2.me/theorems/58207eff-5c83-4306-ba12-222860ff39d4
-- title:
--   Har2: finrank har
-- statement:
--   The Har2 construction uses the finrank har property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L650-L674
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L650-L674

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Har2
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har2.finrank_har [CharZero K] (k' A B : ℕ) :
    Module.finrank K (HarAB K (k' + 1) (A + 1) (B + 1)) + Module.finrank K (PolAB K (k' + 1) A B) =
      Module.finrank K (PolAB K (k' + 1) (A + 1) (B + 1)) := by sorry
