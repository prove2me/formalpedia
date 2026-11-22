-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_sub
-- name    : Formalism.CountingSumsFrames.Har2.harProj_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:30.899073+00:00
-- url     : https://prove2.me/theorems/003ffde8-f23e-4b80-a1d6-f230d809c6a2
-- title:
--   Har2: har Proj sub
-- statement:
--   The Har2 construction uses the har Proj sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L376-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L376-L389

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

theorem Formalism.CountingSumsFrames.Har2.harProj_sub {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ∃ g ∈ PolAB K k (A - 1) (B - 1), f - harProj K k A B f = hXY K k * g := by sorry
