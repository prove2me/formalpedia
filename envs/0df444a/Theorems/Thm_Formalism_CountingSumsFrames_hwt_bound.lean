-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_hwt_bound
-- name    : Formalism.CountingSumsFrames.hwt_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:45.724736+00:00
-- url     : https://prove2.me/theorems/9be27f9a-6c23-4f61-88dc-afc9d15ed579
-- title:
--   Counting Sums Frames: hwt bound
-- statement:
--   The Counting Sums Frames construction uses the hwt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/WeylDimPosOfAntitone.lean#L150-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/WeylDimPosOfAntitone.lean#L150-L192

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.hwt_bound (m A c B : ℕ) (t : ℝ) (ht : 0 ≤ t) (hA : (c : ℝ) ≤ t * A) (hB : (c : ℝ) ≤ t * B) :
    (weylDim (m + 2) (hwt m (A + c) (B + c)) : ℝ) ≤ (1 + t) ^ (2 * m + 1) * (weylDim (m + 2) (hwt m A B) : ℝ) := by sorry
