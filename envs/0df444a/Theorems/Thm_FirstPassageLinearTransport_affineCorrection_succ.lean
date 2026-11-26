-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_affineCorrection_succ
-- name    : FirstPassageLinearTransport.affineCorrection_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:02:08.378152+00:00
-- url     : https://prove2.me/theorems/dfbc2718-3a92-4688-97f7-e23390c94374
-- title:
--   First Passage Linear Transport: affine Correction succ
-- statement:
--   The First Passage Linear Transport construction uses the affine Correction succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L181-L201
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L181-L201

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.affineCorrection_succ (n k : ℕ) :
    affineCorrection n (k + 1) =
      3 ^ (parityBit n k : ℕ) * affineCorrection n k +
        (parityBit n k : ℕ) * 2 ^ k := by sorry
