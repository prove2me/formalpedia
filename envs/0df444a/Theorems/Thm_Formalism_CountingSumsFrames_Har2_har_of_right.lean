-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_of_right
-- name    : Formalism.CountingSumsFrames.Har2.har_of_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:48.567496+00:00
-- url     : https://prove2.me/theorems/4b97c214-f63f-4753-8425-f761991c93eb
-- title:
--   Har2: har of right
-- statement:
--   The Har2 construction uses the har of right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L401-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L401-L402

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
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har2.har_of_right {A : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A 0) : f ∈ HarAB K k A 0 := by sorry
