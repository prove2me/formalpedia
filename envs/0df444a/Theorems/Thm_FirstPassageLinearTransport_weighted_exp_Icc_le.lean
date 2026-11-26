-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_weighted_exp_Icc_le
-- name    : FirstPassageLinearTransport.weighted_exp_Icc_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:43.38232+00:00
-- url     : https://prove2.me/theorems/5a6bf0b1-3a74-41b4-8b61-afe897332f61
-- title:
--   First Passage Linear Transport: weighted exp Icc le
-- statement:
--   Finite weighted exponential tails retain every strict smaller rate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTail.lean#L72-L108
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTail.lean#L72-L108

import Mathlib.Algebra.Order.Field.GeomSum
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.weighted_exp_Icc_le
    {c c' : ℝ} (hc' : 0 < c') (hcc' : c' < c) (L U : ℕ) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      weightedTailConstant c c' * Real.exp (-(c' * (L : ℝ))) := by sorry
