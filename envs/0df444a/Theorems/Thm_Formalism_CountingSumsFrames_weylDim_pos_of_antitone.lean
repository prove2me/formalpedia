-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_weylDim_pos_of_antitone
-- name    : Formalism.CountingSumsFrames.weylDim_pos_of_antitone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:40.570999+00:00
-- url     : https://prove2.me/theorems/45d0f631-f73e-470f-88a4-0837868d7944
-- title:
--   Counting Sums Frames: weyl Dim pos of antitone
-- statement:
--   The Counting Sums Frames construction uses the weyl Dim pos of antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/WeylDimPosOfAntitone.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/WeylDimPosOfAntitone.lean#L38-L48

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

theorem Formalism.CountingSumsFrames.weylDim_pos_of_antitone (m : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) : 0 < weylDim m μ := by sorry
