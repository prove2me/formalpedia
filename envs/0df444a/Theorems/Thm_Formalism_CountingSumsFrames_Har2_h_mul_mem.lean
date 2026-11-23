-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_h_mul_mem
-- name    : Formalism.CountingSumsFrames.Har2.h_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:36.716179+00:00
-- url     : https://prove2.me/theorems/cd607392-3316-4aa7-a48e-cbb16b59abbd
-- title:
--   Har2: h mul mem
-- statement:
--   The Har2 construction uses the h mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L69-L73

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

theorem Formalism.CountingSumsFrames.Har2.h_mul_mem {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    hXY K k * f ∈ PolAB K k (A + 1) (B + 1) := by sorry
