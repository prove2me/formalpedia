-- Prove2me | Theorems.Thm_BianchiIX_eraAmplitude_le
-- name    : BianchiIX.eraAmplitude_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:03:09.357967+00:00
-- url     : https://prove2.me/theorems/1fa441e7-4c8f-4897-ad83-5b85a93a0417
-- title:
--   Every era amplitude is bounded by the initial amplitude
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   If $0\leq B\leq1$, then $M_m(B)\leq B$ for every $m$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L22-L23

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

theorem BianchiIX.eraAmplitude_le {B : ℝ} (hB : 0 ≤ B) (hB1 : B ≤ 1) (m : ℕ) : eraAmplitude B m ≤ B := by sorry
