-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_tail_q_bound
-- name    : Formalism.CountingSumsFrames.tail_q_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:14.818778+00:00
-- url     : https://prove2.me/theorems/4425cddd-d967-4483-bef3-e41db26f6fce
-- title:
--   Counting Sums Frames: tail q bound
-- statement:
--   The Counting Sums Frames construction uses the tail q bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/BinomialSeriesBound.lean#L143-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/BinomialSeriesBound.lean#L143-L186

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

theorem Formalism.CountingSumsFrames.tail_q_bound (k' be : ℕ) (b' : ℝ) (hk : 1 ≤ k') (_hb : 0 < b') :
    ∀ J : ℕ, (be : ℝ) + J + k' ≤ 2 * b' →
      (dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J)
        ≤ ((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b')) := by sorry
