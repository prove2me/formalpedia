-- Prove2me | Theorems.Thm_BianchiIX_eraAmplitude_zero
-- name    : BianchiIX.eraAmplitude_zero
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:03:06.835249+00:00
-- url     : https://prove2.me/theorems/5b59e291-22fc-4b77-ba4c-4b32a2ad1007
-- title:
--   The initial era amplitude
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   For every real $B$, $M_0(B)=B$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L16-L17

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX
open Filter
open scoped Topology

@[simp] theorem BianchiIX.eraAmplitude_zero (B : ℝ) : eraAmplitude B 0 = B := by sorry
