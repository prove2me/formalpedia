-- Prove2me | Theorems.Thm_BianchiIX_amplitude_halving_of_small_beta
-- name    : BianchiIX.amplitude_halving_of_small_beta
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:04:34.657047+00:00
-- url     : https://prove2.me/theorems/fdb2a418-e3c3-4c7b-9c10-04ba6fed414e
-- title:
--   A small power of the amplitude gives a halving factor
-- statement:
--   If $B\geq0$ and $B^\eta<1/160$, then $B^{\eta/3}\leq1/2$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L43-L54

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

theorem BianchiIX.amplitude_halving_of_small_beta {B η : ℝ} (hB : 0 ≤ B)
    (hsmall : B ^ η < 1 / 160) : B ^ (η / 3) ≤ 1 / 2 := by sorry
