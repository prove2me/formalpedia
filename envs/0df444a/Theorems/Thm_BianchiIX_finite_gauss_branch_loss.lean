-- Prove2me | Theorems.Thm_BianchiIX_finite_gauss_branch_loss
-- name    : BianchiIX.finite_gauss_branch_loss
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:28:10.172417+00:00
-- url     : https://prove2.me/theorems/b7e0422d-5cc7-4acd-a755-df89438d71d7
-- title:
--   A finite-digit loss bound from summable inverse-branch endpoint errors
-- statement:
--   Let $N\in\mathbb N$, $0\leq\beta\leq1/2$, $E\geq0$,
--   and real endpoint sequences $L_m,R_m$ satisfy, for $m<N$,
--   $$\frac1{m+2}<R_m<L_m<\frac1{m+1},$$
--   $$|L_m-1/(m+1+2\beta)|\leq E/(m+1)^2,$$
--   $$|R_m-1/(m+2-2\beta)|\leq E/(m+1)^2.$$
--   Then the open intervals $(R_m,L_m)$ are pairwise disjoint and their
--   complement in $(0,1)$ is measurable, with
--   $$\lambda\left((0,1)\setminus\bigcup_{m<N}(R_m,L_m)\right)
--   \leq\frac1{N+1}+8\beta+4E.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Measure/GaussBranchLoss.lean#L14-L83

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_EraReturnData
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

theorem BianchiIX.finite_gauss_branch_loss {N : ℕ} {β E : ℝ} {L R : ℕ → ℝ}
    (hβ : 0 ≤ β) (hβmax : β ≤ 1 / 2) (hE : 0 ≤ E)
    (horder : ∀ m ∈ Finset.range N, R m < L m)
    (hlower : ∀ m ∈ Finset.range N, 1 / ((m : ℝ) + 2) < R m)
    (hupper : ∀ m ∈ Finset.range N, L m < 1 / ((m : ℝ) + 1))
    (hL : ∀ m ∈ Finset.range N,
      |L m - gaussInv ((m : ℝ) + 1) (2 * β)| ≤ E / ((m : ℝ) + 1) ^ 2)
    (hR : ∀ m ∈ Finset.range N,
      |R m - gaussInv ((m : ℝ) + 1) (1 - 2 * β)| ≤ E / ((m : ℝ) + 1) ^ 2) :
    (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (fun m => Ioo (R m) (L m)) ∧
    MeasurableSet (Ioo (0 : ℝ) 1 \ retainedBranchPhases N L R) ∧
    volume (Ioo (0 : ℝ) 1 \ retainedBranchPhases N L R) ≤
      ENNReal.ofReal (1 / ((N : ℝ) + 1) + 8 * β + 4 * E) := by sorry
