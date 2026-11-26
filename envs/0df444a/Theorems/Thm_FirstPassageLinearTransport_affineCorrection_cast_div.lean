-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_affineCorrection_cast_div
-- name    : FirstPassageLinearTransport.affineCorrection_cast_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:02:05.05152+00:00
-- url     : https://prove2.me/theorems/8e1b06aa-a201-5c89-af3f-a75a0bbe06b5
-- title:
--   First Passage Linear Transport: affine Correction cast div
-- statement:
--   The First Passage Linear Transport construction uses the affine Correction cast div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L241-L253
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L241-L253

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.affineCorrection_cast_div (n k : ℕ) :
    (affineCorrection n k : ℚ) / (2 : ℚ) ^ k = affineCorrectionQ n k := by sorry
