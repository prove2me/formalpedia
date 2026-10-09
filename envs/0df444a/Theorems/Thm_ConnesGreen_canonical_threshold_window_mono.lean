-- Prove2me | Theorems.Thm_ConnesGreen_canonical_threshold_window_mono
-- name    : ConnesGreen.canonical_threshold_window_mono
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T04:50:08.89624+00:00
-- url     : https://prove2.me/theorems/64ccbecb-b627-40da-ac68-edf34c5526f8
-- title:
--   Original sharp selected loss is nondecreasing with support
-- statement:
--   For $0<t\le T$ and the SAME finite ACTUAL zero packet $S$, the sharp loss thresholds of the ORIGINAL completed physical carriers satisfy $$\mu_{t,S}\le\mu_{T,S}.$$ The supported test, its physical energy, the full positive actor and selected negative actor are preserved across windows by the existing certified custody identities. No zero-threshold, RH, or sign hypothesis is supplied.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/ThresholdWindowControl.lean, exact declaration ConnesGreen.canonical_threshold_window_mono, compiling source 2e24e42e6cc679c8adb75393a6edf8ba511dc28f

import Definitions.Def_ConnesGreen_sharp_certificate_threshold
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability

theorem ConnesGreen.canonical_threshold_window_mono (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) :
    canonicalCertificateThreshold t ht S ≤ canonicalCertificateThreshold T hT S := by sorry
