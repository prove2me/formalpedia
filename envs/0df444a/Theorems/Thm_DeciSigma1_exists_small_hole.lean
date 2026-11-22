-- Prove2me | Theorems.Thm_DeciSigma1_exists_small_hole
-- name    : DeciSigma1.exists_small_hole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:26:16.263847+00:00
-- url     : https://prove2.me/theorems/34b3f85a-a069-45e8-9043-7fb78f608204
-- title:
--   Deci Sigma1: exists small hole
-- statement:
--   Every structural reader with `N` states and `k` starts over a finite alphabet that has a
--   hole has one of total length at most `smallHoleBound σ k N`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L400-L404
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L400-L404

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1

theorem DeciSigma1.exists_small_hole {α S : Type} [Fintype α] [DecidableEq α] [Fintype S]
    [DecidableEq S] {k : ℕ} (M : Readers.StructuralReader α S k) (h : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧
      Readers.totalLength W ≤ smallHoleBound (Fintype.card α) k (Fintype.card S) := by sorry
