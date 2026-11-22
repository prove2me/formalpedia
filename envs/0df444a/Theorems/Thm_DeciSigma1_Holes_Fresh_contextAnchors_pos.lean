-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_pos
-- name    : DeciSigma1.Holes.Fresh.contextAnchors_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:28.571345+00:00
-- url     : https://prove2.me/theorems/11755799-a381-49e6-8b86-1a638a912692
-- title:
--   Fresh: context Anchors pos
-- statement:
--   No context anchor lies at the cut `0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L281-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L281-L289

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.contextAnchors_pos {W : Fin k → List α} {t : ℕ} {u : List α} {e : ℕ}
    (h : e ∈ contextAnchors W t u) : 1 ≤ e := by sorry
