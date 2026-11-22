-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_multiplicity_le
-- name    : Formalism.CountingSumsFrames.sizeBound_multiplicity_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:54.143719+00:00
-- url     : https://prove2.me/theorems/23ca14d3-dd6e-400a-8d8a-b4ac743b944d
-- title:
--   Counting Sums Frames: size Bound multiplicity le
-- statement:
--   The Counting Sums Frames construction uses the size Bound multiplicity le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SecondParameterSizeBoundsHolds.lean#L35-L47

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

theorem Formalism.CountingSumsFrames.sizeBound_multiplicity_le (r k Q c' al : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hk8 : 8 ≤ k) (hc : 1 ≤ c')
    (hal : al ≤ 1 + r * k * Q) :
    (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' ≤ 3 * r * k * c' * Q := by sorry
