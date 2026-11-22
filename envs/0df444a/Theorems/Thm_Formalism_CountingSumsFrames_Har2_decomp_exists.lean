-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_decomp_exists
-- name    : Formalism.CountingSumsFrames.Har2.decomp_exists
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:06.982617+00:00
-- url     : https://prove2.me/theorems/46d70bcc-4d1c-4969-9998-4fad595f1f47
-- title:
--   Har2: decomp exists
-- statement:
--   The Har2 construction uses the decomp exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L404-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L404-L443

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

theorem Formalism.CountingSumsFrames.Har2.decomp_exists [CharZero K] (hk : 1 ≤ k) : ∀ (A B : ℕ) (f : PolXY K k), f ∈ PolAB K k A B →
    ∃ w : ℕ → PolXY K k, (∀ j, w j ∈ HarAB K k (A - j) (B - j)) ∧
      f = ∑ j ∈ range (min A B + 1), hXY K k ^ j * w j := by sorry
