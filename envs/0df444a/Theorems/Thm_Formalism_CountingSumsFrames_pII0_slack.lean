-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pII0_slack
-- name    : Formalism.CountingSumsFrames.pII0_slack
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:42.070634+00:00
-- url     : https://prove2.me/theorems/7e6536a2-35d1-4d8a-ac54-79bce385cc35
-- title:
--   Counting Sums Frames: p II0 slack
-- statement:
--   The Counting Sums Frames construction uses the p II0 slack property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L193-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L193-L217

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

theorem Formalism.CountingSumsFrames.pII0_slack (r N N₁ k Q c' Y al c₀ : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hrN1 : r ≤ N₁)
    (hN1 : N₁ ^ 2 ≤ r * N) (hk : N₁ + 3 * r ≤ k) (hc : 1 ≤ c') (hY : 0 ≤ Y)
    (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) (hc00 : 0 ≤ c₀) (hc0 : c₀ ≤ c') :
    (100 * r ^ 2 * c' + 24 * (N₁ + r) * c₀ +
        (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1) * (Y * k ^ 2 * Q)
      ≤ 155 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by sorry
