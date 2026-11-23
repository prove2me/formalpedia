-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_image
-- name    : Formalism.CountingSumsFrames.Har2.levelProj_image
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:06.051701+00:00
-- url     : https://prove2.me/theorems/5f52ce36-d44c-410b-8074-f1d6fea62caa
-- title:
--   Har2: level Proj image
-- statement:
--   The Har2 construction uses the level Proj image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L498-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L498-L503

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

theorem Formalism.CountingSumsFrames.Har2.levelProj_image [CharZero K] (hk : 1 ≤ k) {A B : ℕ} (j : ℕ) {f : PolXY K k}
    (hf : f ∈ PolAB K k A B) :
    ∃ w ∈ HarAB K k (A - j) (B - j), levelProj K k A B j f = hXY K k ^ j * w := by sorry
