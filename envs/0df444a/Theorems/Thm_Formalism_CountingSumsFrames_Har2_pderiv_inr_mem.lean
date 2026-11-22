-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inr_mem
-- name    : Formalism.CountingSumsFrames.Har2.pderiv_inr_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:48.954839+00:00
-- url     : https://prove2.me/theorems/3b99854a-33f9-4f7a-8005-55f8e5c7c0b4
-- title:
--   Har2: pderiv inr mem
-- statement:
--   The Har2 construction uses the pderiv inr mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L103-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L103-L114

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

theorem Formalism.CountingSumsFrames.Har2.pderiv_inr_mem {A B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    pderiv (Sum.inr i) f ∈ PolAB K k A (B - 1) := by sorry
