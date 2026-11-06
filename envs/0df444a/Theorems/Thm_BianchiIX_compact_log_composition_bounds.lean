-- Prove2me | Theorems.Thm_BianchiIX_compact_log_composition_bounds
-- name    : BianchiIX.compact_log_composition_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:48:31.296008+00:00
-- url     : https://prove2.me/theorems/56834487-f8e2-4be3-b3eb-02c09e6d8fee
-- title:
--   Compact logarithmic composition controls the weak row without the strong-wall error
-- statement:
--   Let $J:\mathbb R^4\to\mathbb R^2$ be linear, with
--   $J_{ij}=(Je_j)_i$, and let $A,B\geq0$, $u,v>0$, $\ell,s,t\geq0$,
--   and $L\leq A+\ell$. For $d\in\mathbb R^4$, assume
--   $$|d_0|,|d_1|\leq A,\quad |d_1|\leq u(A+s),\quad
--   |d_2|\leq v(A+t),\quad d_3=0,$$
--   $$|J_{00}|,|J_{10}|\leq BL,\quad |J_{01}-1/u|\leq B,\quad
--   |J_{02}|\leq4B/v,\quad |J_{11}|\leq B,\quad |J_{12}|\leq B/v.$$
--   For $C=BA^2+6BA+A+4B+1$,
--   $$|(Jd)_0|\leq C(1+\ell+s+t),\qquad |(Jd)_1|\leq C(1+\ell+t).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactLogComposition.lean#L10-L73

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Real.Sqrt

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.compact_log_composition_bounds
    (J : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (d : Fin 4 → ℝ)
    {A B u v L ℓ s t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : 0 < u) (hv : 0 < v)
    (hℓ : 0 ≤ ℓ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hlog : L ≤ A + ℓ)
    (hd0 : |d 0| ≤ A) (hd1 : |d 1| ≤ A)
    (hdu : |d 1| ≤ u * (A + s)) (hdv : |d 2| ≤ v * (A + t)) (hd3 : d 3 = 0)
    (hUr : |J (Pi.single 0 1) 0| ≤ B * L)
    (hUu : |J (Pi.single 1 1) 0 - 1 / u| ≤ B)
    (hUv : |J (Pi.single 2 1) 0| ≤ 4 * B / v)
    (hWr : |J (Pi.single 0 1) 1| ≤ B * L)
    (hWu : |J (Pi.single 1 1) 1| ≤ B)
    (hWv : |J (Pi.single 2 1) 1| ≤ B / v) :
    let C := B * A ^ 2 + 6 * (B * A) + A + 4 * B + 1
    |J d 0| ≤ C * (1 + ℓ + s + t) ∧ |J d 1| ≤ C * (1 + ℓ + t) := by sorry
