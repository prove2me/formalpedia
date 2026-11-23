-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_partial
-- name    : Formalism.CountingSumsFrames.Har2.ctr_partial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:06.899777+00:00
-- url     : https://prove2.me/theorems/3c04dd3e-3f58-4825-9c80-83a71703cbb1
-- title:
--   Har2: ctr partial
-- statement:
--   The Har2 construction uses the ctr partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L338-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L338-L355

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

theorem Formalism.CountingSumsFrames.Har2.ctr_partial [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) (N : ℕ)
    (hN : N ≤ min A B) :
    ctrF K k (∑ l ∈ range (N + 1), cP K (A + B + k - 2) l • (hXY K k ^ l * (ctrF K k ^ l) f)) =
      cP K (A + B + k - 2) N • (hXY K k ^ N * (ctrF K k ^ (N + 1)) f) := by sorry
