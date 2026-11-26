-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_endpointJump_cube_dom_of_overlap_formula
-- name    : Auto.aux_CuboidNorm.endpointJump_cube_dom_of_overlap_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:29.553276+00:00
-- url     : https://prove2.me/theorems/9388aee0-e836-48d7-8946-0838da3e80e7
-- title:
--   aux Cuboid Norm: endpoint Jump cube dom of overlap formula
-- statement:
--   The overlap formula gives the pointwise endpoint-jump domination needed
--   for the finite base-cube energy comparison.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1878-L1907
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1878-L1907

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.endpointJump_cube_dom_of_overlap_formula {n J : ℕ}
    {ε δ : ℝ} (hεδ : ε ≤ δ)
    (N : Fin (J + 1) → ℕ) (T : ℕ → RVector n → ℝ)
    (D : ℕ → ZVector n → ℝ) (W : RVector n → ℝ)
    (hW : ∀ u, (∀ i, 0 ≤ u i ∧ u i ≤ ε) → δ - ε ≤ W u)
    (hT : ∀ (M : ℕ) (k : ZVector n) (u : RVector n),
      (∀ i, 0 ≤ u i ∧ u i < ε) →
      0 < M →
      T M (fun i ↦ (k i : ℝ) + u i) = W u * D M k)
    (hNpos : ∀ q, 0 < N q)
    (j : Fin J) (k : ZVector n) (x : RVector n)
    (hx : x ∈ latticeCuboid ε k) :
    ‖(δ - ε) * (D (N j.succ) k - D (N j.castSucc) k)‖ₑ ≤
      ‖(T (N j.succ) x - T (N j.castSucc) x)‖ₑ := by sorry
