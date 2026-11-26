-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_PowerDense_mono_constant
-- name    : FirstPassageLinearTransport.PowerDense.mono_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:57:09.069493+00:00
-- url     : https://prove2.me/theorems/e454b71d-97d6-4b74-a5e5-c3302f092f97
-- title:
--   Power Dense: mono constant
-- statement:
--   The Power Dense construction uses the mono constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L37-L44
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L37-L44

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.PowerDense.mono_constant {S : Set ℕ} {C C' D : ℝ}
    (h : PowerDense S C D) (hCC' : C ≤ C') :
    PowerDense S C' D := by sorry
