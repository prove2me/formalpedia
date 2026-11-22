-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_h_pow_mul_mem
-- name    : Formalism.CountingSumsFrames.Har2.h_pow_mul_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:46.113398+00:00
-- url     : https://prove2.me/theorems/578630c5-313c-417c-b158-36a26c15094e
-- title:
--   Har2: h pow mul mem
-- statement:
--   The Har2 construction uses the h pow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L75-L81

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

theorem Formalism.CountingSumsFrames.Har2.h_pow_mul_mem {A B : ℕ} (l : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    hXY K k ^ l * f ∈ PolAB K k (A + l) (B + l) := by sorry
