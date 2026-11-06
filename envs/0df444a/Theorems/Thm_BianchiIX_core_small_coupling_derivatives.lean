-- Prove2me | Theorems.Thm_BianchiIX_core_small_coupling_derivatives
-- name    : BianchiIX.core_small_coupling_derivatives
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:58:30.927651+00:00
-- url     : https://prove2.me/theorems/fbc31fec-0149-4495-8ca1-c6ecac90251d
-- title:
--   Bounds for the radius and strong-wall derivatives of the coupling
-- statement:
--   Suppose $r\geq5$, $0\leq\varepsilon\leq1/100$,
--   $0\leq u,w\leq\varepsilon$, $1\leq v\leq r$, and $0\leq s\leq1$.
--   Then
--   $$|u(s-w/r)|\leq u,\qquad |v-2u+w|\leq2r.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreCoefficientEstimates.lean#L120-L132

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.core_small_coupling_derivatives {r m u v w s : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v ∧ v ≤ r) (hs : 0 ≤ s ∧ s ≤ 1) :
    |u * (s - w / r)| ≤ u ∧ |v - 2 * u + w| ≤ 2 * r := by sorry
