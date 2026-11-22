-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_h_pow
-- name    : Formalism.CountingSumsFrames.Har2.ctr_h_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:22.900512+00:00
-- url     : https://prove2.me/theorems/fb02f9fb-9247-40cd-80ab-9d01aec53335
-- title:
--   Har2: ctr h pow
-- statement:
--   The Har2 construction uses the ctr h pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L236-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L236-L249

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

theorem Formalism.CountingSumsFrames.Har2.ctr_h_pow {a b : ℕ} (l : ℕ) {g : PolXY K k} (hg : g ∈ PolAB K k a b) :
    ctrF K k (hXY K k ^ (l + 1) * g) = hXY K k ^ (l + 1) * ctrF K k g +
      (((l + 1) * (a + b + k + l) : ℕ) : K) • (hXY K k ^ l * g) := by sorry
