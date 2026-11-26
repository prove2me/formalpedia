-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_sqrt_mul_log_le_linear
-- name    : FirstPassageLinearTransport.eventually_sqrt_mul_log_le_linear
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:38:15.383813+00:00
-- url     : https://prove2.me/theorems/1eb35f08-21d0-47c0-be10-792aaf91d677
-- title:
--   First Passage Linear Transport: eventually sqrt mul log le linear
-- statement:
--   The square-root logarithmic time corridor is little-oh of the source
--   rank, in a coefficient-sensitive form.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AsymptoticBounds.lean#L25-L58
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AsymptoticBounds.lean#L25-L58

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_sqrt_mul_log_le_linear
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ≤
        delta * ((M : ℝ) + 2) := by sorry
