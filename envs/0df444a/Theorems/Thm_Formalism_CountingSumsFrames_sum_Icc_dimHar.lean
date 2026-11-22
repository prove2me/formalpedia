-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sum_Icc_dimHar
-- name    : Formalism.CountingSumsFrames.sum_Icc_dimHar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:59.748039+00:00
-- url     : https://prove2.me/theorems/9d2634e4-ea1e-454d-9fa7-89f4381dc82a
-- title:
--   Counting Sums Frames: sum Icc dim Har
-- statement:
--   The Counting Sums Frames construction uses the sum Icc dim Har property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicLevelCountRec.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicLevelCountRec.lean#L49-L60

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
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
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.sum_Icc_dimHar (k' A B J : ℕ) (hJ : J ≤ min A B) :
    ∑ j ∈ Icc J (min A B), dimHar k' (A - j) (B - j) = dimPol k' (A - J) * dimPol k' (B - J) := by sorry
