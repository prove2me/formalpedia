-- Prove2me | Theorems.Thm_Conway99Formal_TwoSidedSchur_full_gram_bound_of_blocks
-- name    : Conway99Formal.TwoSidedSchur.full_gram_bound_of_blocks
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T01:24:50.252441+00:00
-- url     : https://prove2.me/theorems/76163de7-1bf2-44b3-a052-070745b51b2c
-- title:
--   Sharp full Gram bound from one literal complementary block pair
-- statement:
--   For one finite real K/W/R triple, if both displayed complementary block matrices are positive semidefinite, then the squared norm of the exact cross matrix [K_GH,W_GH] acting on every vector is at most 196 times the vector squared norm. The graph-derived PSD premises remain open.
-- source:
--   Local pinned source: adversarial-review-r230/scratchpad/theorem_hunt/cycle_core_residual_theorem/breakthrough_exceptional_two_sided_schur.md, SHA-256 a6aa4d71010e9382cec7fd055f48a3a9907265f13aeb150d4dddd015fe00c18d. Both PSD premises refer to one K/W/R; deriving them from an actual rooted graph remains open.

import Definitions.Def_Conway99_TwoSidedSchurPureBlocks_20261003
set_option autoImplicit false

theorem Conway99Formal.TwoSidedSchur.full_gram_bound_of_blocks {g h : Type*} [Fintype g] [Fintype h] [DecidableEq g] [DecidableEq h] (K : Matrix (g ⊕ h) (g ⊕ h) ℝ) (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ) (hc : (Conway99Formal.TwoSidedSchur.firstBlock K W R).PosSemidef) (hp : (Conway99Formal.TwoSidedSchur.secondBlock K W R).PosSemidef) (y : h ⊕ h → ℝ) : Conway99Formal.TwoSidedSchur.normSq (Conway99Formal.TwoSidedSchur.action (Conway99Formal.TwoSidedSchur.goodCross K W) y) ≤ 196 * Conway99Formal.TwoSidedSchur.normSq y := by sorry
