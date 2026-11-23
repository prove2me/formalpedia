-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_third_term
-- name    : Formalism.CountingSumsFrames.sizeBound_third_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:14.160804+00:00
-- url     : https://prove2.me/theorems/951732c2-06eb-4c33-82c3-9c0f6737d21d
-- title:
--   Counting Sums Frames: size Bound third term
-- statement:
--   The Counting Sums Frames construction uses the size Bound third term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L162-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L162-L180

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real

theorem Formalism.CountingSumsFrames.sizeBound_third_term (r N N₁ k Q c' Y al : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hk8 : 8 ≤ k) (hc : 1 ≤ c')
    (hY : 0 ≤ Y) (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) (hN0 : 0 ≤ N) (hN10 : 0 ≤ N₁)
    (hN1r : N₁ + 1 ≤ 2 * r * N) :
    (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
      ≤ 6 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by sorry
