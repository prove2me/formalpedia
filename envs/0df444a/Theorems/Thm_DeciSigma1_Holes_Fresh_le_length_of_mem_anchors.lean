-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_le_length_of_mem_anchors
-- name    : DeciSigma1.Holes.Fresh.le_length_of_mem_anchors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:09.663451+00:00
-- url     : https://prove2.me/theorems/fea9cb74-8ca0-4303-8d35-ff02a1a39c6f
-- title:
--   Fresh: le length of mem anchors
-- statement:
--   Anchors of a coordinate are cuts of its word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L292-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L292-L296

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

theorem DeciSigma1.Holes.Fresh.le_length_of_mem_anchors {W : Fin k → List α} {t : ℕ} {l : Fin k} {p : ℕ}
    (hp : p ∈ anchors W t l) : p ≤ (W l).length := by sorry
