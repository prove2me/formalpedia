-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_indep
-- name    : Formalism.CountingSumsFrames.Har2.har_indep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:32.697127+00:00
-- url     : https://prove2.me/theorems/62583815-9321-4ee3-9254-5215017a4038
-- title:
--   Har2: har indep
-- statement:
--   The Har2 construction uses the har indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L279-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L279-L304

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

theorem Formalism.CountingSumsFrames.Har2.har_indep [CharZero K] (hk : 1 ≤ k) (n : ℕ) : ∀ (a b : ℕ → ℕ) (w : ℕ → PolXY K k),
    (∀ j, w j ∈ HarAB K k (a j) (b j)) → ∑ j ∈ range n, hXY K k ^ j * w j = 0 → ∀ j < n, w j = 0 := by sorry
