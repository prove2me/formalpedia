-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_PowerDense_degrade_exponent
-- name    : FirstPassageLinearTransport.PowerDense.degrade_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:57:19.650707+00:00
-- url     : https://prove2.me/theorems/3651e6a2-1cd5-5753-ab4d-e7c50fc1c5ab
-- title:
--   Power Dense: degrade exponent
-- statement:
--   The Power Dense construction uses the degrade exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L46-L55
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L46-L55

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.PowerDense.degrade_exponent {S : Set ℕ} {C D D' : ℝ}
    (h : PowerDense S C D) (hD' : 0 < D') (hD'D : D' ≤ D) :
    PowerDense S C D' := by sorry
