-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_one_le_quadratic_startup_factor
-- name    : FirstPassageLinearTransport.one_le_quadratic_startup_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:12.049192+00:00
-- url     : https://prove2.me/theorems/8454b449-ea83-4d68-8b83-00c523c877ba
-- title:
--   First Passage Linear Transport: one le quadratic startup factor
-- statement:
--   The First Passage Linear Transport construction uses the one le quadratic startup factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L186-L212
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L186-L212

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.one_le_quadratic_startup_factor
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hsmall : ¬(4 ≤ M ∧ 2 ≤ t * M)) :
    1 ≤ quadraticWindowShellConstant *
      Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) := by sorry
