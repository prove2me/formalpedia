-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_h
-- name    : Formalism.CountingSumsFrames.Har2.ctr_h
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:33:21.722982+00:00
-- url     : https://prove2.me/theorems/e44b3539-d585-4ce1-aa22-efdba53cd129
-- title:
--   Har2: ctr h
-- statement:
--   The Har2 construction uses the ctr h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L222-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L222-L234

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

theorem Formalism.CountingSumsFrames.Har2.ctr_h {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrF K k (hXY K k * f) = hXY K k * ctrF K k f + ((A + B + k : ℕ) : K) • f := by sorry
