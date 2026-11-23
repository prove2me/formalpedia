-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inr_zero
-- name    : Formalism.CountingSumsFrames.Har2.pderiv_inr_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:25.845881+00:00
-- url     : https://prove2.me/theorems/cb840958-7e50-4bf0-84e6-45122a963cef
-- title:
--   Har2: pderiv inr zero
-- statement:
--   The Har2 construction uses the pderiv inr zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L133-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L133-L140

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

theorem Formalism.CountingSumsFrames.Har2.pderiv_inr_zero {A : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A 0) :
    pderiv (Sum.inr i) f = 0 := by sorry
