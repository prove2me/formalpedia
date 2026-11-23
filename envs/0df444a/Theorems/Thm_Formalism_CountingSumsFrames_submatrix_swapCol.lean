-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_submatrix_swapCol
-- name    : Formalism.CountingSumsFrames.submatrix_swapCol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:19.096537+00:00
-- url     : https://prove2.me/theorems/c528dd17-1b0b-4976-ae06-2a99d2b21aac
-- title:
--   Counting Sums Frames: submatrix swap Col
-- statement:
--   The Counting Sums Frames construction uses the submatrix swap Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ExistsNonzeroExchangedMinorHolds.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/ExistsNonzeroExchangedMinorHolds.lean#L8-L15

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset Matrix
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.submatrix_swapCol {R : Type} [CommRing R] {r k : ℕ} (h : r ≤ k) (H : Matrix (Fin r) (Fin k) R)
    (i : Fin r) (c : Fin k) :
    H.submatrix id (swapCol r k h i c) = (H.submatrix id (Fin.castLE h)).updateCol i (fun m => H m c) := by sorry
