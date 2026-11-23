-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_euler_X_sum
-- name    : Formalism.CountingSumsFrames.Har2.euler_X_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:19.808981+00:00
-- url     : https://prove2.me/theorems/082dcda1-7f96-4869-a697-e749fd48abd0
-- title:
--   Har2: euler X sum
-- statement:
--   The Har2 construction uses the euler X sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L198-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L198-L208

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

theorem Formalism.CountingSumsFrames.Har2.euler_X_sum {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ∑ i : Fin k, X (Sum.inl i) * pderiv (Sum.inl i) f = (A : K) • f := by sorry
