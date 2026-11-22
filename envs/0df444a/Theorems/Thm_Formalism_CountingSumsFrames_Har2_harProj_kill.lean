-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_kill
-- name    : Formalism.CountingSumsFrames.Har2.harProj_kill
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:29.710669+00:00
-- url     : https://prove2.me/theorems/89c39912-5a50-4232-917b-d7ec7a66665b
-- title:
--   Har2: har Proj kill
-- statement:
--   The Har2 construction uses the har Proj kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L463-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L463-L469

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

theorem Formalism.CountingSumsFrames.Har2.harProj_kill [CharZero K] (hk : 1 ≤ k) {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) {g : PolXY K k}
    (hg : g ∈ PolAB K k (A - 1) (B - 1)) : harProj K k A B (hXY K k * g) = 0 := by sorry
