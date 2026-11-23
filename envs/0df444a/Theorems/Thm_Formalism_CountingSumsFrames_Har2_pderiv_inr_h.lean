-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inr_h
-- name    : Formalism.CountingSumsFrames.Har2.pderiv_inr_h
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:26.082081+00:00
-- url     : https://prove2.me/theorems/4230a5d5-b600-4c7d-a7d4-f944f4a24e10
-- title:
--   Har2: pderiv inr h
-- statement:
--   The Har2 construction uses the pderiv inr h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L182-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L182-L184

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

theorem Formalism.CountingSumsFrames.Har2.pderiv_inr_h (i : Fin k) : pderiv (Sum.inr i) (hXY K k) = X (Sum.inl i) := by sorry
