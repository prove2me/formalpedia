-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inl_zero
-- name    : Formalism.CountingSumsFrames.Har2.pderiv_inl_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:13.629706+00:00
-- url     : https://prove2.me/theorems/1fbae397-038a-426c-b47e-4da4788af33f
-- title:
--   Har2: pderiv inl zero
-- statement:
--   The Har2 construction uses the pderiv inl zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L124-L131

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

theorem Formalism.CountingSumsFrames.Har2.pderiv_inl_zero {B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k 0 B) :
    pderiv (Sum.inl i) f = 0 := by sorry
