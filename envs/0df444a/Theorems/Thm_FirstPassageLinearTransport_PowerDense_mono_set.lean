-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_PowerDense_mono_set
-- name    : FirstPassageLinearTransport.PowerDense.mono_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:57:29.876046+00:00
-- url     : https://prove2.me/theorems/08671a3f-d210-4902-a37e-c68194987e7d
-- title:
--   Power Dense: mono set
-- statement:
--   The Power Dense construction uses the mono set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L57-L74
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L57-L74

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.PowerDense.mono_set {S T : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) (hST : S ⊆ T) :
    PowerDense T C D := by sorry
