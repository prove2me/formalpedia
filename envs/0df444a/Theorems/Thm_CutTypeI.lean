-- Prove2me | Theorems.Thm_CutTypeI
-- name    : CutTypeI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:38.723237+00:00
-- url     : https://prove2.me/theorems/2595be80-1d8f-5604-8e7b-9766be07bdbc
-- title:
--   Cut Type I: Cut Type I
-- statement:
--   Paper Lemma 3.8's Type~I cut operation (paper.tex 798-913), existential form, consuming the
--   cut point `(t,t',β)` produced by `TypeICutPointExists`: for `0 < ε < 1`, `0 < δ`, and a closed
--   piecewise-geodesic curve `γ` that is a `(δ,ε,n)`-curve (`IsDeltaEpsN`) but is *not*
--   `(δ,ε)`-large-scale-invertible (`IsLSI`), there exist closed piecewise-geodesic curves `γ'`
--   (kept) and `g` (discarded) and a real `β ∈ [δ,γ.len/2]` such that `[[γ]] = [[γ']] + [[g]]`, `g`
--   admits the ball growth bound `Morrey(g) ≤ 4ε⁻¹+2n+10`, `γ',g` satisfy the two length bounds
--   `γ'.len ≤ γ.len-(1-ε)β` and `γ'.len+g.len ≤ γ.len+2εβ`, and `γ'` has at most `3` more small edges
--   than `γ`. Stated existentially in `(γ',g,β)` and never mentioning the cut points `t,t'`
--   themselves, matching `TypeICutPointExists`'s own no-choice-function existential form: nothing
--   downstream of Lemma 3.8 needs `(γ',g,β)` to be a definite function of `γ`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CutTypeI.lean#L50-L264
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CutTypeI.lean#L50-L264

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_TypeICutPointExists
import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_BasicCutClosed
import Definitions.Def_Tablet_BasicCutCurrent
import Definitions.Def_Tablet_BasicCutLength
import Definitions.Def_Tablet_BasicCutResolutionGeneral
import Definitions.Def_Tablet_BasicCutDiscardedResolutionGeneral
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_ArcShortWindowEdgeCount
import Definitions.Def_Tablet_ArcDeltaEpsNCount
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_FullBallLem
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_RestrictLSI
import Definitions.Def_Tablet_RestrictFullIsSelf
import Definitions.Def_Tablet_RestrictMeasureFormula
import Definitions.Def_Tablet_MorreyResolutionAdditive
import Definitions.Def_Tablet_MorreySubadditive
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutDiscardedEval
import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_CutTypeI
import Theorems.Thm_ArcDeltaEpsNCount
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_ArcShortWindowEdgeCount
import Theorems.Thm_BasicCutClosed
import Theorems.Thm_BasicCutCurrent
import Theorems.Thm_BasicCutDiscardedEval
import Theorems.Thm_BasicCutDiscardedResolutionGeneral
import Theorems.Thm_BasicCutLength
import Theorems.Thm_BasicCutResolutionGeneral
import Theorems.Thm_C1SmallBall
import Theorems.Thm_FullBallLem
import Theorems.Thm_GeodesicMorreyLeTwo
import Theorems.Thm_MorreyResolutionAdditive
import Theorems.Thm_MorreySubadditive
import Theorems.Thm_RestrictFullIsSelf
import Theorems.Thm_RestrictLSI
import Theorems.Thm_RestrictMeasureFormula
import Theorems.Thm_RestrictPiecewiseGeodesic
import Theorems.Thm_TypeICutPointExists

set_option autoImplicit false
open Set ENNReal

theorem CutTypeI {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (δ ε : ℝ) (n : ℕ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ)
    (hden : IsDeltaEpsN γ δ ε n) (hnlsi : ¬ IsLSI γ δ ε) :
    ∃ (γ' g : Curve E) (β : ℝ),
      δ ≤ β ∧ β ≤ γ.len / 2 ∧
      (∀ ω : Form1 E, curveCurrent γ ω = curveCurrent γ' ω + curveCurrent g ω) ∧
      IsClosedCurve γ' ∧ IsPiecewiseGeodesic γ' ∧
      IsClosedCurve g ∧ IsPiecewiseGeodesic g ∧
      morreyNorm (curveMeasure g) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 10) ∧
      γ'.len ≤ γ.len - (1 - ε) * β ∧
      γ'.len + g.len ≤ γ.len + 2 * ε * β ∧
      smallPieceCount γ' δ ≤ smallPieceCount γ δ + 3 := by sorry
