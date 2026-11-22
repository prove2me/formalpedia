-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_of_left
-- name    : Formalism.CountingSumsFrames.Har2.har_of_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:39.922792+00:00
-- url     : https://prove2.me/theorems/98f1a95b-b5d8-44ef-ae52-2375b5f64ee1
-- title:
--   Har2: har of left
-- statement:
--   The Har2 construction uses the har of left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L398-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L398-L399

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

theorem Formalism.CountingSumsFrames.Har2.har_of_left {B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k 0 B) : f ∈ HarAB K k 0 B := by sorry
