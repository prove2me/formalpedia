-- Prove2me | Theorems.Thm_BianchiIX_connection_weak_cone_size
-- name    : BianchiIX.connection_weak_cone_size
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:51:25.527346+00:00
-- url     : https://prove2.me/theorems/f2685f19-9706-4f3f-ab18-c6d4b7d86c53
-- title:
--   The weak connection row retains an exponential cone margin
-- statement:
--   Let $\mu\geq4$, $0\leq u\leq1$, $w>0$, $L\geq256$,
--   and $40000\sqrt w\leq1$. Then
--   $$\sqrt w\,e^{-L/\mu}\left(
--   \frac{274L}{\mu^2}+\frac{9000(1+L)\sqrt u}{\mu^2}
--   +\frac{1+32/\mu}{w}\sqrt w\right)
--   \leq e^{-L/(2\mu)}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/ConnectionConeSize.lean#L97-L142

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.connection_weak_cone_size {μ u w L : ℝ} (hμ : 4 ≤ μ) (hu : 0 ≤ u ∧ u ≤ 1)
    (hw : 0 < w) (hL : 256 ≤ L) (hsmall : 40000 * Real.sqrt w ≤ 1) :
    (Real.sqrt w * Real.exp (-L / μ)) *
      (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u +
        (1 + 32 / μ) / w * Real.sqrt w) ≤ Real.exp (-L / (2 * μ)) := by sorry
