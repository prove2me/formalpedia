-- Prove2me | Theorems.Thm_BianchiIX_extension_amplitude_gain
-- name    : BianchiIX.extension_amplitude_gain
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:38:06.544118+00:00
-- url     : https://prove2.me/theorems/f4ffb092-51e0-4823-bf3b-b381af4c45da
-- title:
--   The amplitude gain after extension
-- statement:
--   Suppose $0<B\leq B_{\max}$, $C\geq0$, and
--   $\tfrac{25}{16}CB_{\max}^{17/30}\leq1$. Then
--   $$\tfrac{25}{16}(CB^{19/10})\leq B^{4/3}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/SmallParameters.lean#L24-L30

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.extension_amplitude_gain {B Bmax C : ℝ} (hB : 0 < B) (hmax : B ≤ Bmax)
    (hC : 0 ≤ C) (hbudget : (25 / 16 : ℝ) * C * Bmax ^ (17 / 30 : ℝ) ≤ 1) :
    (25 / 16 : ℝ) * (C * B ^ (19 / 10 : ℝ)) ≤ B ^ (4 / 3 : ℝ) := by sorry
