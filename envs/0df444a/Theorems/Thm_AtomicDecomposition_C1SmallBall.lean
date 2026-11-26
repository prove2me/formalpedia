-- Prove2me | Theorems.Thm_AtomicDecomposition_C1SmallBall
-- name    : AtomicDecomposition.C1SmallBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:03.605285+00:00
-- url     : https://prove2.me/theorems/cf468a29-ead8-4fa8-9806-2c9787a08dd3
-- title:
--   Atomic Decomposition: C1 Small Ball
-- statement:
--   The Atomic Decomposition construction uses the C1 Small Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Solution.lean#L162-L166
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Solution.lean#L162-L166

import Definitions.Def_Tablet_ApproximationMetric
import Definitions.Def_Tablet_BBAssertion
import Definitions.Def_Tablet_SurgeryEta
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_EtaRepeats
import Definitions.Def_MetricSurgery_Solution
import Theorems.Thm_ApproximationMetric
import Theorems.Thm_BBAssertion
import Theorems.Thm_C1SmallBall
import Theorems.Thm_EtaRepeats
import Theorems.Thm_SurgeryEta

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open AtomicDecomposition

theorem AtomicDecomposition.C1SmallBall {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (hpw : IsPiecewiseGeodesicWith γ k) :
    morreyNorm (curveMeasure γ) ≤ 2 * (k : ℝ≥0∞)
    := by sorry
