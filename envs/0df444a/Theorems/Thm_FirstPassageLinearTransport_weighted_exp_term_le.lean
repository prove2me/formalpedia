-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_weighted_exp_term_le
-- name    : FirstPassageLinearTransport.weighted_exp_term_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:31.177912+00:00
-- url     : https://prove2.me/theorems/86e0404b-18bb-4f33-bd21-1553d1b75187
-- title:
--   First Passage Linear Transport: weighted exp term le
-- statement:
--   The First Passage Linear Transport construction uses the weighted exp term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTail.lean#L29-L69
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTail.lean#L29-L69

import Mathlib.Algebra.Order.Field.GeomSum
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.weighted_exp_term_le
    {c c' : ℝ} (hcc' : c' < c) (q : ℕ) :
    ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      (1 + 1 / (c - c')) * (Real.exp (-c')) ^ q := by sorry
