-- Prove2me | Theorems.Thm_DetDLP_d4_unroll_tree_bit_budget
-- name    : DetDLP.d4_unroll_tree_bit_budget
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T08:36:59.405734+00:00
-- url     : https://prove2.me/theorems/01aa76cb-947b-4201-90da-5979e6282470
-- title:
--   Bit budget for adaptive depth-bounded 64-child unrolling
-- statement:
--   For every worklist that expands one adaptive radix at a time, enqueues all 64 children, and doubles their total edge mass, the binary rank tree fits an explicit computable budget. The budget is bounded by a constant times b/L^(7/40)+L^(13/10), uniformly in the choice histories. This is the rank-padding form of the tree count in Lemma 5.3(i).

import Definitions.Def_DetDLP_D4UnrollBudget
import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan DetDLP.D3Stopped DetDLP.AppendixD4 DetDLP.D4RankCode DetDLP.D4UnrollBudget

theorem DetDLP.d4_unroll_tree_bit_budget (C K : ℕ) (hC : 0<C) : ∃ L₀ Ktot : ℕ, ∀ {c : ℕ} (x : Input C c),
    let L := D3Stopped.level x.S; let D := Nat.clog 32 (4*x.m); let B := budget x.S D K
    L₀ ≤ L → ((B:ℝ) ≤ Ktot*((x.b:ℝ)/(L:ℝ)^(7/40:ℝ)+(L:ℝ)^(13/10:ℝ))) ∧
      ((2:ℝ)^B ≤ Real.exp (Ktot*((x.b:ℝ)/(L:ℝ)^(7/40:ℝ)+(L:ℝ)^(13/10:ℝ)))) ∧
      ∀ {α : Type} {M : ℕ} {t : D4RankCode.Tree α}, M ≤ x.S → Work x.S D K [(0,M)] t → t.Fits B := by sorry
