-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrDiv_mem
-- name    : Formalism.CountingSumsFrames.Har2.ctrDiv_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:33:05.921525+00:00
-- url     : https://prove2.me/theorems/6cfce1b4-cbd5-4fe1-94c5-88695c1035d2
-- title:
--   Har2: ctr Div mem
-- statement:
--   The Har2 construction uses the ctr Div mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L493-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L493-L496

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

theorem Formalism.CountingSumsFrames.Har2.ctrDiv_mem {A B : ℕ} (j : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrDiv K k j f ∈ PolAB K k (A - j) (B - j) := by sorry
