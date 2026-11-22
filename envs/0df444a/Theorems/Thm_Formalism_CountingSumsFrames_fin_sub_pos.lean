-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fin_sub_pos
-- name    : Formalism.CountingSumsFrames.fin_sub_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:01.176316+00:00
-- url     : https://prove2.me/theorems/82efd9b8-163b-44eb-8efe-b008a9869153
-- title:
--   Counting Sums Frames: fin sub pos
-- statement:
--   The Counting Sums Frames construction uses the fin sub pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/WeylDimPosOfAntitone.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/WeylDimPosOfAntitone.lean#L76-L78

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

theorem Formalism.CountingSumsFrames.fin_sub_pos (m : ℕ) (j : Fin m) : 0 < (m : ℝ) - ((j : ℕ) : ℝ) := by sorry
