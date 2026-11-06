-- Prove2me | Theorems.Thm_BianchiIX_gauss_error_finite
-- name    : BianchiIX.gauss_error_finite
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:10:00.4042+00:00
-- url     : https://prove2.me/theorems/4b54c7f4-b5b5-4594-8262-eb263f63bf58
-- title:
--   Finite expansion of the inverse recurrence error
-- statement:
--   Let $(a_m)_{m\geq0}$ be natural numbers with $a_m\geq1$ and write
--   $g_a(x)=1/(a+x)$. For real sequences $y,z$, define
--   $$e_m=|y_m-g_{a_m}(y_{m+1})|,\qquad E_m=|y_m-z_m|.$$
--   The exact comparison sequence satisfies $z_m=g_{a_m}(z_{m+1})$ for every $m$.
--
--   Suppose $y_m,z_m\geq0$ for all $m$. For every $m,N\in\mathbb N$,
--   $$E_m\leq\sum_{j=0}^{N-1}4^{-j}(e_{m+2j}+e_{m+2j+1})+4^{-N}E_{m+2N}.$$
--   The expansion keeps the actual terminal discrepancy.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussInverse.lean#L153-L177

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

theorem BianchiIX.gauss_error_finite {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, 0 ≤ y m) (hz : ∀ m, 0 ≤ z m)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m N : ℕ) :
    |y m - z m| ≤
      (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j *
        (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) +
      (1 / 4 : ℝ) ^ N * |y (m + 2 * N) - z (m + 2 * N)| := by sorry
