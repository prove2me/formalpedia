-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_vecSumTriples_le
-- name    : ArithmeticTriangleRemovalInVectorSpaces.card_vecSumTriples_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:55.96991+00:00
-- url     : https://prove2.me/theorems/c3d7fdcf-bf84-4839-9bd2-7634d5de9823
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: card vec Sum Triples le
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the card vec Sum Triples le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Hash.lean#L103-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Hash.lean#L103-L104

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Hash
set_option autoImplicit true
@[expose] public section
public section
open Finset Matrix
open ArithmeticTriangleRemovalInVectorSpaces
variable {n p P F : ℕ}
variable {A B C : Finset (Fin n → ℕ)} {V : Finset ((Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ))}
  {S : Finset (ZMod P)} {θ : (Fin n → ZMod P) × ZMod P × ZMod P}
  {v v' : (Fin n → ℕ) × (Fin n → ℕ) × (Fin n → ℕ)} {a b c a' b' c' : Fin n → ℕ}

theorem ArithmeticTriangleRemovalInVectorSpaces.card_vecSumTriples_le : #(vecSumTriples p A B C) ≤ #A * #B * #C := by sorry
