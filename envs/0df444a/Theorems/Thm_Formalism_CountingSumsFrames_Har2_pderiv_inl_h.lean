-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inl_h
-- name    : Formalism.CountingSumsFrames.Har2.pderiv_inl_h
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:42.345771+00:00
-- url     : https://prove2.me/theorems/a6b79545-19b6-4d5a-a250-8a495481a95d
-- title:
--   Har2: pderiv inl h
-- statement:
--   The Har2 construction uses the pderiv inl h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L186-L188

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

theorem Formalism.CountingSumsFrames.Har2.pderiv_inl_h (i : Fin k) : pderiv (Sum.inl i) (hXY K k) = X (Sum.inr i) := by sorry
