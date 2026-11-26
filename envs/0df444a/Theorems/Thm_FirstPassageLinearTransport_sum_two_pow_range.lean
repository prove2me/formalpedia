-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sum_two_pow_range
-- name    : FirstPassageLinearTransport.sum_two_pow_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:28.921637+00:00
-- url     : https://prove2.me/theorems/c52eb4e9-e90e-4ffc-a381-33714dbaf70d
-- title:
--   First Passage Linear Transport: sum two pow range
-- statement:
--   The First Passage Linear Transport construction uses the sum two pow range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/VaryingDensity.lean#L103-L106
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/VaryingDensity.lean#L103-L106

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.sum_two_pow_range (L : ℕ) :
    ∑ j ∈ Finset.range L, (2 : ℝ) ^ j = (2 : ℝ) ^ L - 1 := by sorry
