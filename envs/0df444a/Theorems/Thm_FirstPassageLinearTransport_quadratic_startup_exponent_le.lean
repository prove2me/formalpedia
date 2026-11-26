-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_quadratic_startup_exponent_le
-- name    : FirstPassageLinearTransport.quadratic_startup_exponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:04.826941+00:00
-- url     : https://prove2.me/theorems/c31ac4c2-ef6e-41df-bcf3-ae77d72f85d6
-- title:
--   First Passage Linear Transport: quadratic startup exponent le
-- statement:
--   The First Passage Linear Transport construction uses the quadratic startup exponent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L169-L184
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L169-L184

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.quadratic_startup_exponent_le
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hsmall : ¬(4 ≤ M ∧ 2 ≤ t * M)) :
    maximalBarrierC0 * t ^ 2 * M ≤ 4 * maximalBarrierC0 := by sorry
