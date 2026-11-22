-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_monomial_mem
-- name    : Formalism.CountingSumsFrames.Har2.monomial_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:28.777797+00:00
-- url     : https://prove2.me/theorems/9698d72b-cfa3-41f7-8212-092b877cb6a2
-- title:
--   Har2: monomial mem
-- statement:
--   The Har2 construction uses the monomial mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L15-L20

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

theorem Formalism.CountingSumsFrames.Har2.monomial_mem {A B : ℕ} {m : XY k →₀ ℕ} (c : K) (hx : xDeg m = A) (hy : yDeg m = B) :
    monomial m c ∈ PolAB K k A B := by sorry
