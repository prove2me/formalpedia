-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pII0_size
-- name    : Formalism.CountingSumsFrames.pII0_size
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:31.066809+00:00
-- url     : https://prove2.me/theorems/77ea234d-1848-4f18-954d-8f1add006180
-- title:
--   Counting Sums Frames: p II0 size
-- statement:
--   The Counting Sums Frames construction uses the p II0 size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L73-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L73-L129

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

theorem Formalism.CountingSumsFrames.pII0_size (CE p r N N₁ Nₛ k Q c' Y al : ℝ) (hCE : 0 ≤ CE) (hp : 0 ≤ p) (hpQ : p ≤ Q)
    (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N) (hk : N₁ + 3 * r ≤ k)
    (hNs0 : 0 ≤ Nₛ) (hNs1 : Nₛ ≤ N₁) (hNs2 : Nₛ ≤ 2 * N) (hc : 1 ≤ c') (hY : 0 ≤ Y)
    (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) :
    32 * p * Y * k ^ 2 * Nₛ * Q ^ 2 *
        (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1)
      ≤ 32 * (2 * CE + 7) * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by sorry
