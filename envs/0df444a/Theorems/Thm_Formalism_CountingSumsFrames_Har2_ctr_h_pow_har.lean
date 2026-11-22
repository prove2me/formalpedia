-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_h_pow_har
-- name    : Formalism.CountingSumsFrames.Har2.ctr_h_pow_har
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:27.465904+00:00
-- url     : https://prove2.me/theorems/127d390e-cc1f-466b-9d71-4c0cc73a1d69
-- title:
--   Har2: ctr h pow har
-- statement:
--   The Har2 construction uses the ctr h pow har property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L254-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L254-L256

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

theorem Formalism.CountingSumsFrames.Har2.ctr_h_pow_har {a b : ℕ} (i : ℕ) {w : PolXY K k} (hw : w ∈ HarAB K k a b) :
    ctrF K k (hXY K k ^ (i + 1) * w) = (((i + 1) * (a + b + k + i) : ℕ) : K) • (hXY K k ^ i * w) := by sorry
