-- Prove2me | Theorems.Thm_BianchiIX_gauss_error_infinite
-- name    : BianchiIX.gauss_error_infinite
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:11:54.938371+00:00
-- url     : https://prove2.me/theorems/fb229d8a-bcab-4ca1-9b16-156ced143c41
-- title:
--   Infinite inverse recurrence error estimate
-- statement:
--   Let $(a_m)_{m\geq0}$ be natural numbers with $a_m\geq1$ and write
--   $g_a(x)=1/(a+x)$. For real sequences $y,z$, define
--   $$e_m=|y_m-g_{a_m}(y_{m+1})|,\qquad E_m=|y_m-z_m|.$$
--   The exact comparison sequence satisfies $z_m=g_{a_m}(z_{m+1})$ for every $m$.
--
--   Suppose $y_m,z_m\in[0,1]$ for every $m$. Then
--   $$E_m\leq\sum_{j=0}^{\infty}4^{-j}(e_{m+2j}+e_{m+2j+1})\qquad(m\in\mathbb N).$$
--   This bounds the discrepancy from the exact recurrence by the future local errors.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussInverse.lean#L218-L229

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

theorem BianchiIX.gauss_error_infinite {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m)
    (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (hz : ∀ m, z m ∈ Set.Icc (0 : ℝ) 1)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m : ℕ) :
    |y m - z m| ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ j *
      (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1)) := by sorry
