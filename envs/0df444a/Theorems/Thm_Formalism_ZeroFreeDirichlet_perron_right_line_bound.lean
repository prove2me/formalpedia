-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_right_line_bound
-- name    : Formalism.ZeroFreeDirichlet.perron_right_line_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:43:53.984006+00:00
-- url     : https://prove2.me/theorems/d18cbef8-602c-4e46-a73e-59264186ad30
-- title:
--   Zero Free Dirichlet: perron right line bound
-- statement:
--   The Zero Free Dirichlet construction uses the perron right line bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L21-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronHorizontalSegmentBound.lean#L21-L57

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

theorem Formalism.ZeroFreeDirichlet.perron_right_line_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C₀ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y T t : ℝ) (hy : 1 < y) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖Fchi χ y (((1 + 1 / Real.log y : ℝ) : ℂ) + t * I)‖ ≤
      (Real.log y + C₀) * (Real.exp 1 * y) / t ^ 2 := by sorry
