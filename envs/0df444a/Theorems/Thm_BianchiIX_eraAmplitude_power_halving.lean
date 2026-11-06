-- Prove2me | Theorems.Thm_BianchiIX_eraAmplitude_power_halving
-- name    : BianchiIX.eraAmplitude_power_halving
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:08:46.788475+00:00
-- url     : https://prove2.me/theorems/b89ec776-a5ea-4043-9693-c72a80292f1b
-- title:
--   Geometric contraction of powered era amplitudes
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   Suppose $0<B\leq1$, $p\geq0$, and
--   $B^{p/3}\leq1/2$. Then
--   $$M_{m+1}(B)^p\leq\tfrac12M_m(B)^p.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L56-L63

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

theorem BianchiIX.eraAmplitude_power_halving {B p : ℝ} (hB : 0 < B) (hB1 : B ≤ 1) (hp : 0 ≤ p)
    (hsmall : B ^ (p / 3) ≤ 1 / 2) (m : ℕ) :
    eraAmplitude B (m + 1) ^ p ≤ (1 / 2) * eraAmplitude B m ^ p := by sorry
