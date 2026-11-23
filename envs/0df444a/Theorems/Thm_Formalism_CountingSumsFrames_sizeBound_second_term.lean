-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_second_term
-- name    : Formalism.CountingSumsFrames.sizeBound_second_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:23.511983+00:00
-- url     : https://prove2.me/theorems/dac1f304-d4fb-40f8-9645-d123f2ab732c
-- title:
--   Counting Sums Frames: size Bound second term
-- statement:
--   The Counting Sums Frames construction uses the size Bound second term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L143-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L143-L160

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

theorem Formalism.CountingSumsFrames.sizeBound_second_term (r N N₁ k Q c' Y c₀ : ℝ) (hr : 1 ≤ r) (hN : 1 ≤ N) (hk0 : 0 ≤ k) (hQ : 1 ≤ Q)
    (hY : 0 ≤ Y) (hNk : N₁ + r ≤ k) (hc00 : 0 ≤ c₀) (hc0 : c₀ ≤ c') :
    (N₁ + r) * c₀ * (Y * k ^ 2 * Q) ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by sorry
