-- Prove2me | Theorems.Thm_BitDFT_multiplier_time_linear
-- name    : BitDFT.multiplier_time_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:40:43.80621+00:00
-- url     : https://prove2.me/theorems/47ea6c79-58c1-4ed4-8310-cd0e6ae172fd
-- title:
--   Every binary multiplier pays for its full product output
-- statement:
--   If a machine correctly multiplies all pairs of $s$-bit inputs within a real time bound $T$, with exactly $2s$ output bits, then
--   $$2s\le T.$$
--   This pointwise bound justifies absorbing linear input/output work into the cost of any correct multiplication machine, even when its runtime function has no monotonicity or regularity properties.
-- source:
--   Immediate specialization of the output-size lower bound to IntMul.MultipliesAt; the linear-work absorption used in Harvey–van der Hoeven 2025, Lemma 3.2, https://arxiv.org/html/2503.22848v1#S3.SS4.

import Definitions.Def_IntMul_MultitapeModel
set_option autoImplicit false
open IntMul

theorem BitDFT.multiplier_time_linear (M : MultitapeTM) (s : ℕ) (T : ℝ)
    (h : MultipliesAt M s T) : (2 * s : ℕ) ≤ T := by sorry
