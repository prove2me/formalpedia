-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_sum_le_of_card_le_one
-- name    : Formalism.ZeroFreeDirichlet.norm_sum_le_of_card_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:33.655981+00:00
-- url     : https://prove2.me/theorems/569d353c-3038-47dc-b9f2-bc56f6f423c1
-- title:
--   Zero Free Dirichlet: norm sum le of card le one
-- statement:
--   The Zero Free Dirichlet construction uses the norm sum le of card le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L14-L19

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.norm_sum_le_of_card_le_one (B : Finset ℝ) (hB : B.card ≤ 1) (f : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ β ∈ B, ‖f β‖ ≤ M) : ‖∑ β ∈ B, f β‖ ≤ M := by sorry
