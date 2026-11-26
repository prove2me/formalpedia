-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_PowerDense_bad_bound
-- name    : FirstPassageLinearTransport.PowerDense.bad_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:34.396915+00:00
-- url     : https://prove2.me/theorems/0a64d526-641d-4147-8939-6371dbad522d
-- title:
--   Power Dense: bad bound
-- statement:
--   The Power Dense construction uses the bad bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L32-L35
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L32-L35

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.PowerDense.bad_bound {S : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) (X : ℕ) (hX : 1 ≤ X) :
    (badCount S X : ℝ) ≤ C * (X : ℝ) ^ (1 - D) := by sorry
