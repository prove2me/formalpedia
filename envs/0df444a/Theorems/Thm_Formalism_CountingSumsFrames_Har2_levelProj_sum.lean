-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_sum
-- name    : Formalism.CountingSumsFrames.Har2.levelProj_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:09.571971+00:00
-- url     : https://prove2.me/theorems/becc9db3-2fd6-4557-bab1-188c028662e9
-- title:
--   Har2: level Proj sum
-- statement:
--   The Har2 construction uses the level Proj sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L540-L553
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L540-L553

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

theorem Formalism.CountingSumsFrames.Har2.levelProj_sum [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ∑ j ∈ range (min A B + 1), levelProj K k A B j f = f := by sorry
