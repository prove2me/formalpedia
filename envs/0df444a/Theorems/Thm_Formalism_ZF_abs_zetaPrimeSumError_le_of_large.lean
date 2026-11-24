-- Prove2me | Theorems.Thm_Formalism_ZF_abs_zetaPrimeSumError_le_of_large
-- name    : Formalism.ZF.abs_zetaPrimeSumError_le_of_large
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:56.080126+00:00
-- url     : https://prove2.me/theorems/3bdf71e1-2093-4d17-b35a-d9063f433501
-- title:
--   ZF: abs zeta Prime Sum Error le of large
-- statement:
--   The ZF construction uses the abs zeta Prime Sum Error le of large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/AbsZetaPrimeSumErrorLeOfLarge.lean#L12-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/AbsZetaPrimeSumErrorLeOfLarge.lean#L12-L198

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_IntegralEqIntervalIntegralAddCompl
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaNeZeroOfMemRectangle
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_AbsZetaPrimeSumErrorLeOfLarge
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
open Formalism Formalism.ZF
set_option maxHeartbeats 1000000

theorem Formalism.ZF.abs_zetaPrimeSumError_le_of_large (c₀ c₁ C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hZ : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (hR : ∀ s : ℂ, 1 < s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C₂)
    (hP : Perron) (hRS : RectShift)
    (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hc0 : c ≤ c₀) (hc1 : c ≤ c₁)
    (y : ℝ) (hy : 2 ≤ y) (hs8 : 8 / c ≤ Real.sqrt (Real.log y))
    (hs1 : 1 ≤ Real.sqrt (Real.log y)) :
    |Formalism.Gz y| ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (C₁ + 1) + 4 * (C₁ + 1)) *
        (6 * (8 / c) ^ 3) * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by sorry
