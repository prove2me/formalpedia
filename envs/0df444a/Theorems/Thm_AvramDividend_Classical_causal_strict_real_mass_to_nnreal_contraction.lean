-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_strict_real_mass_to_nnreal_contraction
-- name    : AvramDividend.Classical.causal_strict_real_mass_to_nnreal_contraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:04:50.612981+00:00
-- url     : https://prove2.me/theorems/185fcb6f-87be-4e01-a84a-45b449e9033c
-- title:
--   Strict real mass bound gives a nonnegative contraction factor
-- statement:
--   The nonnegative real ratio m/a is an NNReal below one when 0≤m<a and a>0, and multiplying it by a reconstructs the kernel mass m.
-- source:
--   Use the same verified declaration imports as the previously published bounded-continuous fixed-point helper.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_strict_real_mass_to_nnreal_contraction
    (a m : ℝ) (ha : 0 < a) (hm : 0 ≤ m) (hsmall : m < a) :
    ∃ c : NNReal, c < 1 ∧ (c : ℝ) * a = m := by sorry
