-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_error_terms_sum_bound
-- name    : Formalism.ZeroFreeDirichlet.perron_error_terms_sum_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:33.418975+00:00
-- url     : https://prove2.me/theorems/f15d986a-522c-4038-b80a-5fb1014f3086
-- title:
--   Zero Free Dirichlet: perron error terms sum bound
-- statement:
--   The Zero Free Dirichlet construction uses the perron error terms sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExpGainFromZeroFreeRegion.lean#L8-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExpGainFromZeroFreeRegion.lean#L8-L68

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ChebyshevCharacterExplicitGeneral
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExpGainFromZeroFreeRegion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.perron_error_terms_sum_bound (C C₀ c₁ y T X L Pw Y ℓ : ℝ) (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hy0 : 0 < y) (hT1 : 1 ≤ T) (hTX : T * X = 1) (hL0 : 0 ≤ L) (hY : 0 ≤ Y)
    (hℓP : ℓ ≤ Pw) (hP1 : 1 ≤ Pw) (hL2P : L ^ 2 ≤ Pw) (hL3P : L ^ 3 ≤ Pw) (hLP : L ≤ Pw) :
    2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T)
        + Y * (8 * L / c₁) ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
        16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁) * Pw * (y * X + T * Y) := by sorry
