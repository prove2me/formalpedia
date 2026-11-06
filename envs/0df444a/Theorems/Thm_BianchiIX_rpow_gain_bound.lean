-- Prove2me | Theorems.Thm_BianchiIX_rpow_gain_bound
-- name    : BianchiIX.rpow_gain_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:32:14.022515+00:00
-- url     : https://prove2.me/theorems/66868b67-19cc-4c17-a63c-2e9d480e7f9e
-- title:
--   Propagation of a power-gain budget to smaller amplitudes
-- statement:
--   Suppose $0<B\leq B_{\max}$, $C\geq0$, $q\leq p$, and
--   $CB_{\max}^{p-q}\leq1$. Then $CB^p\leq B^q$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/SmallParameters.lean#L11-L22

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

theorem BianchiIX.rpow_gain_bound {B Bmax C p q : ℝ} (hB : 0 < B) (hmax : B ≤ Bmax)
    (hC : 0 ≤ C) (hpq : q ≤ p) (hbudget : C * Bmax ^ (p - q) ≤ 1) :
    C * B ^ p ≤ B ^ q := by sorry
