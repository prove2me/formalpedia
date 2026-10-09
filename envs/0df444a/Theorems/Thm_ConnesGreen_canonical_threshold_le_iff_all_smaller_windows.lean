-- Prove2me | Theorems.Thm_ConnesGreen_canonical_threshold_le_iff_all_smaller_windows
-- name    : ConnesGreen.canonical_threshold_le_iff_all_smaller_windows
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T04:50:08.091263+00:00
-- url     : https://prove2.me/theorems/842ce5b8-f260-458e-9da7-a997ce07c22d
-- title:
--   Sharp-loss bounds close at the original inner support endpoint
-- statement:
--   For an ORIGINAL positive support endpoint $T$, unchanged finite ACTUAL zero packet $S$ and any $a\ge0$, $$\mu_{T,S}\le a\quad\Longleftrightarrow\quad\forall\,0<t<T,\ \mu_{t,S}\le a.$$ This closes EVERY common quantitative sharp-loss bound from the strictly smaller original windows. It asserts no right-window continuity or neutral-shell sign control.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/ThresholdWindowControl.lean, exact declaration ConnesGreen.canonical_threshold_le_iff_all_smaller_windows, compiling source 2e24e42e6cc679c8adb75393a6edf8ba511dc28f

import Definitions.Def_ConnesGreen_sharp_certificate_threshold
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability

theorem ConnesGreen.canonical_threshold_le_iff_all_smaller_windows (T : ℝ) (hT : 0 < T)
    (S : Finset CriticalZeros) (a : ℝ) (ha : 0 ≤ a) :
    canonicalCertificateThreshold T hT S ≤ a ↔
    ∀ t : ℝ, ∀ ht : 0 < t, t < T → canonicalCertificateThreshold t ht S ≤ a := by sorry
