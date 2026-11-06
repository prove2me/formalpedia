-- Prove2me | Theorems.Thm_BianchiIX_gauss_shadowing_of_error_tendsto_zero
-- name    : BianchiIX.gauss_shadowing_of_error_tendsto_zero
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:12:52.52499+00:00
-- url     : https://prove2.me/theorems/a94d1f0c-b861-4521-876f-e98beb3c2f75
-- title:
--   Vanishing recurrence error implies asymptotic agreement
-- statement:
--   Let $(a_m)_{m\geq0}$ be natural numbers with $a_m\geq1$ and write
--   $g_a(x)=1/(a+x)$. For real sequences $y,z$, define
--   $$e_m=|y_m-g_{a_m}(y_{m+1})|,\qquad E_m=|y_m-z_m|.$$
--   The exact comparison sequence satisfies $z_m=g_{a_m}(z_{m+1})$ for every $m$.
--
--   Suppose $y_m,z_m\in[0,1]$ for all $m$ and $e_m\to0$. Then
--   $$y_m-z_m\longrightarrow0.$$
--   Approximate inverse recurrences with vanishing local error therefore approach
--   the specified exact comparison sequence.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussInverse.lean#L231-L259

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

theorem BianchiIX.gauss_shadowing_of_error_tendsto_zero {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m)
    (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (hz : ∀ m, z m ∈ Set.Icc (0 : ℝ) 1)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1)))
    (herror : Tendsto (inverseError digits y) atTop (𝓝 0)) :
    Tendsto (fun m => y m - z m) atTop (𝓝 0) := by sorry
