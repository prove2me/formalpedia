-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbitMinimum_le_power_iff_hasFixedPowerDescent
-- name    : FirstPassageLinearTransport.orbitMinimum_le_power_iff_hasFixedPowerDescent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:17.536513+00:00
-- url     : https://prove2.me/theorems/7628bb4c-ee7c-5678-863d-a22c6b7be7ac
-- title:
--   First Passage Linear Transport: orbit Minimum le power iff has Fixed Power Descent
-- statement:
--   The First Passage Linear Transport construction uses the orbit Minimum le power iff has Fixed Power Descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L90-L93
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L90-L93

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.orbitMinimum_le_power_iff_hasFixedPowerDescent {alpha : ℝ} {n : ℕ} :
    (orbitMinimum n : ℝ) ≤ (n : ℝ) ^ alpha ↔
      HasFixedPowerDescent alpha n := by sorry
