-- Prove2me | Theorems.Thm_BianchiIX_intervalRadiusInverse_control
-- name    : BianchiIX.intervalRadiusInverse_control
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:27:44.673702+00:00
-- url     : https://prove2.me/theorems/02bc6b2f-2338-4432-8505-a5dcbda5cc49
-- title:
--   The decreasing interval inverse and its endpoint derivatives
-- statement:
--   Let $a<b$, and let $k$ be $C^1$ at every point of $[a,b]$
--   with $k'<0$ there. Put $J=[k(b),k(a)]$ and
--   $g=\operatorname{invFunOn}k\,[a,b]$. Then $k(b)<k(a)$,
--   $k([a,b])=J$, $g(J)\subset[a,b]$, $g\circ k=\mathrm{id}$ on $[a,b]$,
--   $k\circ g=\mathrm{id}$ on $J$, and the derivative of $g$ within $J$
--   at every $t\in J$ is $1/k'(g(t))$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/IntervalRadiusInverse.lean#L14-L61

import Definitions.Def_BianchiIX_EraReturnData
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.intervalRadiusInverse_control {k : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x)
    (hd : ∀ x ∈ Icc a b, deriv k x < 0) :
    let J := Icc (k b) (k a)
    let g := intervalRadiusInverse k a b
    k b < k a ∧ k '' Icc a b = J ∧ LeftInvOn g k (Icc a b) ∧
      MapsTo g J (Icc a b) ∧ RightInvOn g k J ∧
      ∀ t ∈ J, HasDerivWithinAt g (deriv k (g t))⁻¹ J t := by sorry
