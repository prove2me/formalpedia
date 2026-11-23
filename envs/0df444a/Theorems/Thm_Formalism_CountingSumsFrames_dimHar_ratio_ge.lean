-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_dimHar_ratio_ge
-- name    : Formalism.CountingSumsFrames.dimHar_ratio_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:06.675664+00:00
-- url     : https://prove2.me/theorems/bfbcfdae-2a5f-43a9-a8da-5bab67e432a3
-- title:
--   Counting Sums Frames: dim Har ratio ge
-- statement:
--   The Counting Sums Frames construction uses the dim Har ratio ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/BinomialSeriesBound.lean#L220-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/BinomialSeriesBound.lean#L220-L260

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
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
open Finset Filter Topology
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.dimHar_ratio_ge (k' al be : ℕ) (hk : 2 ≤ k') (hal : 0 < al) :
    1 ≤ (dimHar k' al be : ℝ) / ((dimPol k' al : ℝ) * dimPol k' be)
      * (((be : ℝ) + k') / ((k' : ℝ) - 1)) := by sorry
