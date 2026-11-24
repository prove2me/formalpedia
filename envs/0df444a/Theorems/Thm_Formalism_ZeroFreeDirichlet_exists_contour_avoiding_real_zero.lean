-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_exists_contour_avoiding_real_zero
-- name    : Formalism.ZeroFreeDirichlet.exists_contour_avoiding_real_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:58.243419+00:00
-- url     : https://prove2.me/theorems/5cbcfc3e-2f23-4794-ab20-34cc8b783517
-- title:
--   Zero Free Dirichlet: exists contour avoiding real zero
-- statement:
--   The Zero Free Dirichlet construction uses the exists contour avoiding real zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExistsContourAvoidingRealZero.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExistsContourAvoidingRealZero.lean#L11-L28

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_IntegralEqIntervalIntegralAddCompl
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExistsContourAvoidingRealZero
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

theorem Formalism.ZeroFreeDirichlet.exists_contour_avoiding_real_zero (B : Finset ℝ) (hB : B.card ≤ 1) (L c₁ : ℝ) (hL : 0 < L) (hc₁ : 0 < c₁) :
    ∃ σ₁ : ℝ, (σ₁ = 1 - c₁ / (3 * L) ∨ σ₁ = 1 - c₁ / (4 * L)) ∧
      ∀ β ∈ B, c₁ / (24 * L) ≤ |σ₁ - β| := by sorry
