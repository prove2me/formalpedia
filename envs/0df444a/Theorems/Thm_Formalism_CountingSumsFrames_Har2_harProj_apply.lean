-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_apply
-- name    : Formalism.CountingSumsFrames.Har2.harProj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:55.86091+00:00
-- url     : https://prove2.me/theorems/de09d065-4a36-4faf-b4e8-8dfe194e6c19
-- title:
--   Har2: har Proj apply
-- statement:
--   The Har2 construction uses the har Proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L329-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L329-L336

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

theorem Formalism.CountingSumsFrames.Har2.harProj_apply (A B : ℕ) (f : PolXY K k) : harProj K k A B f =
    ∑ l ∈ range (min A B + 1), cP K (A + B + k - 2) l • (hXY K k ^ l * (ctrF K k ^ l) f) := by sorry
