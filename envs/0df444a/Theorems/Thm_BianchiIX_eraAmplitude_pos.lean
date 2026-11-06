-- Prove2me | Theorems.Thm_BianchiIX_eraAmplitude_pos
-- name    : BianchiIX.eraAmplitude_pos
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:03:09.817017+00:00
-- url     : https://prove2.me/theorems/40d79383-e06f-498a-9ee5-9e23925e4763
-- title:
--   Positivity of every era amplitude
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   If $B>0$, then $M_m(B)>0$ for every $m$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L19-L20

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

theorem BianchiIX.eraAmplitude_pos {B : ℝ} (hB : 0 < B) (m : ℕ) : 0 < eraAmplitude B m := by sorry
