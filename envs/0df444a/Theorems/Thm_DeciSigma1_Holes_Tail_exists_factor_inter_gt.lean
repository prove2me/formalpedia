-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_factor_inter_gt
-- name    : DeciSigma1.Holes.Tail.exists_factor_inter_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:40.631052+00:00
-- url     : https://prove2.me/theorems/054a8e95-8340-4e56-b6ac-852dbb6a8517
-- title:
--   Tail: exists factor inter gt
-- statement:
--   If all but `T` positions of the rejected tail `[J, |w|)` lie in the factors `fs`, and the
--   interval `[x, y)` of the tail has more than `T + |fs| · r` positions, some factor meets it in
--   more than `r` positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L65-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L65-L91

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.exists_factor_inter_gt {w : List α} {fs : List PeriodicFactor} {J T r x y : ℕ}
    (hunc : (uncoveredPositions fs J w.length).card ≤ T) (hJx : J ≤ x) (hy : y ≤ w.length)
    (hlen : T + fs.length * r < y - x) : ∃ f ∈ fs, r < min f.stop y - max f.start x := by sorry
