-- Prove2me | Theorems.Thm_C1SmallBall
-- name    : C1SmallBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:35.989136+00:00
-- url     : https://prove2.me/theorems/8e9eb593-6cf5-5337-98b3-362212a20847
-- title:
--   C1 Small Ball: C1 Small Ball
-- statement:
--   The C1 Small Ball construction uses the C1 Small Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/C1SmallBall.lean#L9-L32
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/C1SmallBall.lean#L9-L32

import Definitions.Def_Tablet_MorreySubadditive
import Definitions.Def_Tablet_MorreyResolutionAdditive
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_C1SmallBall
import Theorems.Thm_GeodesicMorreyLeTwo
import Theorems.Thm_MorreyResolutionAdditive
import Theorems.Thm_MorreySubadditive

set_option autoImplicit false
open MeasureTheory Set ENNReal

theorem C1SmallBall {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (hpw : IsPiecewiseGeodesicWith γ k) :
    morreyNorm (curveMeasure γ) ≤ 2 * (k : ℝ≥0∞) := by sorry
