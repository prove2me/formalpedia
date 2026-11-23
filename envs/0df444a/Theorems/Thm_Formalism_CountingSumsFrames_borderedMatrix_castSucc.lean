-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_borderedMatrix_castSucc
-- name    : Formalism.CountingSumsFrames.borderedMatrix_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:41:39.375852+00:00
-- url     : https://prove2.me/theorems/9b4b7d24-da0f-4f80-bb16-d40c5050cbc5
-- title:
--   Counting Sums Frames: bordered Matrix cast Succ
-- statement:
--   The Counting Sums Frames construction uses the bordered Matrix cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrobeniusDetVanishingHolds.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrobeniusDetVanishingHolds.lean#L21-L24

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
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
open Finset Matrix
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.borderedMatrix_castSucc {R : Type} [CommRing R] (r : ℕ) (ts : Fin r → R) (u : R)
    (T : Matrix (Fin r) (Fin r) R) (b : Fin r → R) (i : Fin (r + 1)) (j : Fin r) :
    borderedMatrix r ts u T b i (Fin.castSucc j) = borderedMatrix r ts 0 T 0 i (Fin.castSucc j) := by sorry
