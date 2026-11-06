-- Prove2me | Theorems.Thm_BianchiIX_eraAmplitude_power_series
-- name    : BianchiIX.eraAmplitude_power_series
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:10:34.826834+00:00
-- url     : https://prove2.me/theorems/dd85dc5f-ea57-4c8e-b754-ba02b95fa077
-- title:
--   A quantitative bound for every powered amplitude tail
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   Suppose $0<B\leq1$, $p\geq0$, and
--   $B^{p/3}\leq1/2$. For every $k\in\mathbb N$, the series
--   $\sum_{m\geq0}M_{m+k}(B)^p$ converges and
--   $$\sum_{m\geq0}M_{m+k}(B)^p\leq2M_k(B)^p.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L83-L92

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

theorem BianchiIX.eraAmplitude_power_series {B p : ℝ} (hB : 0 < B) (hB1 : B ≤ 1) (hp : 0 ≤ p)
    (hsmall : B ^ (p / 3) ≤ 1 / 2) (k : ℕ) :
    (Summable fun m => eraAmplitude B (m + k) ^ p) ∧
      (∑' m, eraAmplitude B (m + k) ^ p) ≤ 2 * eraAmplitude B k ^ p := by sorry
