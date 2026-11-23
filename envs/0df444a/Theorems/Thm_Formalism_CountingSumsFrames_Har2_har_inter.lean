-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_inter
-- name    : Formalism.CountingSumsFrames.Har2.har_inter
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:57.222419+00:00
-- url     : https://prove2.me/theorems/9ee738e4-99f7-4fae-9590-e6bdfde34169
-- title:
--   Har2: har inter
-- statement:
--   The Har2 construction uses the har inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L445-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L445-L461

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

theorem Formalism.CountingSumsFrames.Har2.har_inter [CharZero K] (hk : 1 ≤ k) {A B a b : ℕ} {u g : PolXY K k} (hu : u ∈ HarAB K k A B)
    (hg : g ∈ PolAB K k a b) (h : u = hXY K k * g) : u = 0 := by sorry
