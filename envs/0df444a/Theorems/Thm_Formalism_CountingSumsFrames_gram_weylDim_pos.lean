-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_gram_weylDim_pos
-- name    : Formalism.CountingSumsFrames.gram_weylDim_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:52.442494+00:00
-- url     : https://prove2.me/theorems/36870dac-7ae8-4eeb-9fe5-84d7e33f8104
-- title:
--   Counting Sums Frames: gram weyl Dim pos
-- statement:
--   The Counting Sums Frames construction uses the gram weyl Dim pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FrameMultinomialBoundHolds.lean#L72-L82

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrameMultinomialBoundHolds
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
open Finset Real
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.gram_weylDim_pos (m : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) : 0 < weylDim m μ := by sorry
