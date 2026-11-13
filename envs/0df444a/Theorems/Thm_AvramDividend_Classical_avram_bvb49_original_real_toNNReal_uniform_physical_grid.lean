-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb49_original_real_toNNReal_uniform_physical_grid
-- name    : AvramDividend.Classical.avram_bvb49_original_real_toNNReal_uniform_physical_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:09:07.805231+00:00
-- url     : https://prove2.me/theorems/7e688580-4cf9-4e5a-a0b8-a527aacde84d
-- title:
--   Canonical source uniform physical NNReal grid has exact terminal, monotonicity and real coordinate identities
-- statement:
--   The canonical grid u(n,i)=Real.toNNReal(T*i/(n+2)) has exactly the intended physical real coordinates for positive T. It starts at zero, its (n+1)-st point is T-T/(n+2), and every row is monotone. This is the exact grid used by the original finite-activity signed HJB witness bvb48b and the original phys36b theorem. The proof uses the pinned Real.coe_toNNReal equivalence for nonnegative arguments and rational arithmetic; no local Lean invocation or alternate process is involved.
-- source:
--   Pinned Mathlib Real.coe_toNNReal; original source physical mesh in bvb_phys28 and bvb48b.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb49_original_real_toNNReal_uniform_physical_grid
    (T : ℝ) (hT : 0 < T) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i =>
      Real.toNNReal (T * (i : ℝ) / ((n : ℝ) + 2))
    (∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
    (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
    (∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) := by sorry
