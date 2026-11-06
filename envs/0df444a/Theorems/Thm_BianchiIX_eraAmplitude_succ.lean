-- Prove2me | Theorems.Thm_BianchiIX_eraAmplitude_succ
-- name    : BianchiIX.eraAmplitude_succ
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:03:13.084201+00:00
-- url     : https://prove2.me/theorems/dd537474-6d21-4df5-9326-0ac829ab921e
-- title:
--   The recurrence for era amplitudes
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   If $B\geq0$, then
--   $$M_{m+1}(B)=M_m(B)^{4/3}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L25-L27

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

theorem BianchiIX.eraAmplitude_succ {B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    eraAmplitude B (m + 1) = eraAmplitude B m ^ (4 / 3 : ℝ) := by sorry
