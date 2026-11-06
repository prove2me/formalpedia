-- Prove2me | Theorems.Thm_BianchiIX_eraAmplitude_power_succ
-- name    : BianchiIX.eraAmplitude_power_succ
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:07:05.098124+00:00
-- url     : https://prove2.me/theorems/5e880f19-5029-4e7f-a876-6d6800c9fce3
-- title:
--   A factorization of successive powered amplitudes
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   For $B>0$ and real $p$,
--   $$M_{m+1}(B)^p=M_m(B)^pM_m(B)^{p/3}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L29-L34

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

theorem BianchiIX.eraAmplitude_power_succ {B : ℝ} (hB : 0 < B) (p : ℝ) (m : ℕ) :
    eraAmplitude B (m + 1) ^ p = eraAmplitude B m ^ p * eraAmplitude B m ^ (p / 3) := by sorry
