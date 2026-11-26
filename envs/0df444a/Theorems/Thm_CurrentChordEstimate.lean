-- Prove2me | Theorems.Thm_CurrentChordEstimate
-- name    : CurrentChordEstimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:39.471823+00:00
-- url     : https://prove2.me/theorems/dc634360-47c8-4bf2-b073-3030e5b8354f
-- title:
--   Current Chord Estimate: Current Chord Estimate
-- statement:
--   The current of a curve `σ` against `ω = (f,π)` differs from the "chord" main term
--   `f(σ u) · (π(σ.len) - π(σ 0))`, sampled at an arbitrary `u ∈ [0, σ.len]`, by at most
--   `Lip(f) · Lip(π) · σ.len² / 2`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentChordEstimate.lean#L9-L115
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentChordEstimate.lean#L9-L115

import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_CurrentChordEstimate
import Theorems.Thm_CurveCurrentBound

set_option autoImplicit false
open MeasureTheory intervalIntegral

theorem CurrentChordEstimate {E : Type*} [MetricSpace E] (σ : Curve E) (ω : Form1 E)
    (u : ℝ) (hu0 : 0 ≤ u) (huL : u ≤ σ.len) :
    |curveCurrent σ ω
        - ω.f (σ.toFun u) * (ω.pi (σ.toFun σ.len) - ω.pi (σ.toFun 0))|
      ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * σ.len ^ 2 / 2 := by sorry
