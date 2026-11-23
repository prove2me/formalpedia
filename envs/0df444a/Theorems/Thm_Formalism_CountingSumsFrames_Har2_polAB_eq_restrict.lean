-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_polAB_eq_restrict
-- name    : Formalism.CountingSumsFrames.Har2.polAB_eq_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:25.233846+00:00
-- url     : https://prove2.me/theorems/a976129f-5c83-4b5a-9444-7eb8a8fd8344
-- title:
--   Har2: pol AB eq restrict
-- statement:
--   The Har2 construction uses the pol AB eq restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L612-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L612-L616

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
open Har2
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har2.polAB_eq_restrict (A B : ℕ) :
    PolAB K k A B = restrictSupport K {m : XY k →₀ ℕ | xDeg m = A ∧ yDeg m = B} := by sorry
