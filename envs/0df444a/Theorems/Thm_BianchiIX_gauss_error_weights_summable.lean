-- Prove2me | Theorems.Thm_BianchiIX_gauss_error_weights_summable
-- name    : BianchiIX.gauss_error_weights_summable
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:07:06.80703+00:00
-- url     : https://prove2.me/theorems/47f038cc-0ca7-4502-b5d1-9a3fd17526bc
-- title:
--   Summability of geometrically weighted recurrence errors
-- statement:
--   Let $a_m\in\mathbb N$ with $a_m\geq1$, let $y_m\in[0,1]$, and set
--   $$e_m=|y_m-1/(a_m+y_{m+1})|.$$
--   For each $m\in\mathbb N$, the series
--   $$\sum_{j=0}^{\infty}4^{-j}(e_{m+2j}+e_{m+2j+1})$$
--   is summable. This supplies the convergent majorant used in the infinite error estimate.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussInverse.lean#L202-L216

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section
open Filter
open scoped Topology

theorem BianchiIX.gauss_error_weights_summable {digits : ℕ → ℕ} {y : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    Summable (fun j => (1 / 4 : ℝ) ^ j *
      (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) := by sorry
