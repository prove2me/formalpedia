-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_first_term
-- name    : Formalism.CountingSumsFrames.sizeBound_first_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:57.914033+00:00
-- url     : https://prove2.me/theorems/e3535480-3b28-4cd0-8224-e8ac540a7c12
-- title:
--   Counting Sums Frames: size Bound first term
-- statement:
--   The Counting Sums Frames construction uses the size Bound first term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L131-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L131-L141

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

theorem Formalism.CountingSumsFrames.sizeBound_first_term (r N k Q c' Y : ℝ) (hr : 0 ≤ r) (hN : 1 ≤ N) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hc : 0 ≤ c') (hY : 0 ≤ Y) :
    r ^ 2 * c' * (Y * k ^ 2 * Q) ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by sorry
