-- Prove2me | Theorems.Thm_BianchiIX_eraAmplitude_series_of_small_beta
-- name    : BianchiIX.eraAmplitude_series_of_small_beta
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:12:32.303473+00:00
-- url     : https://prove2.me/theorems/d9799128-ab0a-4bcc-bbbd-893de7d12074
-- title:
--   Amplitude-tail sums from the small-beta condition
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
--   Suppose $0<B\leq1$, $0\leq\eta\leq p$, and
--   $B^\eta<1/160$. Then, for every $k$, the powered amplitude tail is summable and
--   $$\sum_{m\geq0}M_{m+k}(B)^p\leq2M_k(B)^p.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L99-L104

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

theorem BianchiIX.eraAmplitude_series_of_small_beta {B η p : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hη : 0 ≤ η) (hηp : η ≤ p) (hsmall : B ^ η < 1 / 160) (k : ℕ) :
    (Summable fun m => eraAmplitude B (m + k) ^ p) ∧
      (∑' m, eraAmplitude B (m + k) ^ p) ≤ 2 * eraAmplitude B k ^ p := by sorry
