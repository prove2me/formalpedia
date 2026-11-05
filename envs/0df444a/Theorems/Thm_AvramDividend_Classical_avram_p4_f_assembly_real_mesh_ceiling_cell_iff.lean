-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_real_mesh_ceiling_cell_iff
-- name    : AvramDividend.Classical.avram_p4_f_assembly_real_mesh_ceiling_cell_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:46:41.935054+00:00
-- url     : https://prove2.me/theorems/8c01cb9e-7e32-49cd-a54d-6315739b59ff
-- title:
--   Positive-horizon uniform mesh cells are exactly the ceiling-index fibres
-- statement:
--   For positive T and integer k, a real time u has natural ceiling grid index i+1 exactly when it lies in the half-open interval (i*T/k,(i+1)*T/k]. This source-neutral exact analytic bridge identifies the same physical jump times indexed in the P4-F original-source mesh lemmas with the original marked jump measure's time windows.

import Mathlib.Algebra.Order.Floor.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_real_mesh_ceiling_cell_iff
    (u T : ℝ) (hT : 0 < T) (k i : ℕ) (hk : 0 < k) :
    Nat.ceil (u * (k : ℝ) / T) = i + 1 ↔
      (i : ℝ) * T / (k : ℝ) < u ∧
      u ≤ ((i + 1 : ℕ) : ℝ) * T / (k : ℝ) := by sorry
