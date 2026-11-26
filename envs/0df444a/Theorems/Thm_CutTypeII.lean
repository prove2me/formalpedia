-- Prove2me | Theorems.Thm_CutTypeII
-- name    : CutTypeII
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:54.003487+00:00
-- url     : https://prove2.me/theorems/77aa51cb-f519-4ff2-98ee-61df96af80f3
-- title:
--   Cut Type II: Cut Type II
-- statement:
--   Paper Lemma 3.9 (the Type II cut operation), existential form: for `0 < ε < 1`, `0 < δ`, and a
--   closed piecewise-geodesic curve `γ` that fails to be `(δ,ε,n)`-controlled, there exist closed
--   piecewise-geodesic curves `γ'` (kept) and `g` (discarded) with `[[γ]] = [[γ']] + [[g]]`, a Morrey
--   bound on `g`, length bounds on `γ'` and on the total length `γ'.len + g.len`, and a
--   subtraction-free small-edge-count bound `smallPieceCount γ' δ + n ≤ smallPieceCount γ δ`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CutTypeII.lean#L23-L111
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CutTypeII.lean#L23-L111

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_BasicCutClosed
import Definitions.Def_Tablet_BasicCutCurrent
import Definitions.Def_Tablet_BasicCutLength
import Definitions.Def_Tablet_BasicCutDiscardedResolution
import Definitions.Def_Tablet_BasicCutResolutionAtBreakpoints
import Definitions.Def_Tablet_DeltaEpsNFailureAtBreakpoints
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_CutTypeII
import Theorems.Thm_BasicCutClosed
import Theorems.Thm_BasicCutCurrent
import Theorems.Thm_BasicCutDiscardedResolution
import Theorems.Thm_BasicCutLength
import Theorems.Thm_BasicCutResolutionAtBreakpoints
import Theorems.Thm_C1SmallBall
import Theorems.Thm_DeltaEpsNFailureAtBreakpoints

set_option autoImplicit false
open Set ENNReal
set_option maxRecDepth 4000

theorem CutTypeII {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (δ ε : ℝ) (n : ℕ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ)
    (hfail : ¬ IsDeltaEpsN γ δ ε n) :
    ∃ γ' g : Curve E,
      (∀ ω : Form1 E, curveCurrent γ ω = curveCurrent γ' ω + curveCurrent g ω) ∧
      IsClosedCurve γ' ∧ IsPiecewiseGeodesic γ' ∧
      IsClosedCurve g ∧ IsPiecewiseGeodesic g ∧
      morreyNorm (curveMeasure g) ≤ ENNReal.ofReal (2 * ((n : ℝ) + 2 * ε⁻¹ + 2)) ∧
      γ'.len ≤ γ.len ∧
      γ'.len + g.len ≤ γ.len + 4 * ε⁻¹ * δ ∧
      smallPieceCount γ' δ + n ≤ smallPieceCount γ δ := by sorry
