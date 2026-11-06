-- Prove2me | Theorems.Thm_BianchiIX_amplitude_power_budget
-- name    : BianchiIX.amplitude_power_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:04:06.575857+00:00
-- url     : https://prove2.me/theorems/75088bab-2ec7-4d89-94d2-3fc36ad24841
-- title:
--   A uniform bound for the amplitude contraction factor
-- statement:
--   Suppose $0<B\leq B_{\max}\leq1$, $0\leq\eta\leq p$, and
--   $B_{\max}^{\eta/3}\leq1/2$. Then $B^{p/3}\leq1/2$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L36-L41

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

theorem BianchiIX.amplitude_power_budget {B Bmax η p : ℝ} (hB : 0 < B) (hmax : B ≤ Bmax)
    (hmax1 : Bmax ≤ 1) (hη : 0 ≤ η) (hηp : η ≤ p)
    (hsmall : Bmax ^ (η / 3) ≤ 1 / 2) : B ^ (p / 3) ≤ 1 / 2 := by sorry
