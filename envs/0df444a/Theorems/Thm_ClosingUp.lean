-- Prove2me | Theorems.Thm_ClosingUp
-- name    : ClosingUp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:17.1624+00:00
-- url     : https://prove2.me/theorems/a02721a3-5cd9-4670-ae3a-fc875c0b03e3
-- title:
--   Closing Up: Closing Up
-- statement:
--   Closing the loops (paper.tex 1436-1500): given the single remaining diagonal family of
--   `\noderef{BBSamplingDiagonal}` restricted to the two clauses this node actually needs -- the
--   current averages against every `1`-form (clause (I), supplied for every form by
--   `\noderef{DiagonalizationGeneral}` rather than only a countable family) and the endpoint-cutoff
--   mass-marginal averages (clause (II)) -- concatenate the piecewise-geodesic sampling of each
--   `γ l i` with the geodesic closing its ends into a loop `ghat l i`, and let `gbar l i` be that same
--   closing geodesic traversed the other way. Then `ghat l i` is closed and piecewise geodesic of
--   length at most `2l` and also at most `l` plus the length of `gbar l i` (the sharp bound feeding
--   eq. closed2's length half), the current average against `ghat` plus the current average against
--   `gbar` converges to `T ω` for every `1`-form `ω` (paper eq. important_identity), the averaged
--   length of `gbar` vanishes (paper eq. ExtraLengthSmall), and consequently so does the averaged
--   current of `gbar` against every `ω`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ClosingUp.lean#L34-L496
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ClosingUp.lean#L34-L496

import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_SamplingEndpoints
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_SamplingPiecewiseGeodesic
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatPiecewiseGeodesic
import Definitions.Def_Tablet_GeodesicSampledCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_CurrentReverse
import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_ClosingUp
import Theorems.Thm_ConcatPiecewiseGeodesic
import Theorems.Thm_CurrentConcatAdditive
import Theorems.Thm_CurrentReverse
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_GeodesicSampledCurrent
import Theorems.Thm_SamplingEndpoints
import Theorems.Thm_SamplingPiecewiseGeodesic

set_option autoImplicit false
open Set Filter Finset MeasureTheory

theorem ClosingUp {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T) (GP : GeodesicPairing E) (x0 : E)
    (n : ℕ → ℕ) (hn_pos : ∀ l : ℕ, 0 < n l)
    (γ : ℕ → ℕ → Curve E)
    (hlen : ∀ l : ℕ, 1 ≤ l → ∀ i < n l, (γ l i).len = (l : ℝ))
    (hcur : ∀ ω : Form1 E, Tendsto (fun l : ℕ =>
        (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
          ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω)
        atTop (nhds (T ω)))
    (hend : ∀ r : ℚ, 0 < r →
      (Tendsto (fun l : ℕ => (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
          (if (r : ℝ) ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)) atTop
        (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
          (F.massMeasure {x : E | (r : ℝ) ≤ dist x x0}).toReal)))
      ∧ (Tendsto (fun l : ℕ => (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
          (if (r : ℝ) ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0)) atTop
        (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
          (F.massMeasure {x : E | (r : ℝ) ≤ dist x x0}).toReal)))) :
    ∃ (ghat gbar : ℕ → ℕ → Curve E) (k : ℕ → ℕ → ℕ),
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsClosedCurve (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsPiecewiseGeodesicWith (ghat l i) (k l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (ghat l i).len ≤ 2 * (l : ℝ)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (ghat l i).len ≤ (l : ℝ) + (gbar l i).len) ∧
      (∀ ω : Form1 E, Tendsto (fun l : ℕ =>
          (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
            (∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω
              + ∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω))
          atTop (nhds (T ω))) ∧
      (Tendsto (fun l : ℕ =>
          (1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (gbar l i).len)
          atTop (nhds 0)) ∧
      (∀ ω : Form1 E, Tendsto (fun l : ℕ =>
          (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
            ∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω)
          atTop (nhds 0)) := by sorry
