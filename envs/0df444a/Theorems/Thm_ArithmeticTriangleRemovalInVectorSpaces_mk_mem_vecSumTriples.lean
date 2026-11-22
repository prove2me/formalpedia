-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mk_mem_vecSumTriples
-- name    : ArithmeticTriangleRemovalInVectorSpaces.mk_mem_vecSumTriples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:15.439373+00:00
-- url     : https://prove2.me/theorems/041a3546-0da0-404f-8091-b8b9ac111a14
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: mk mem vec Sum Triples
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the mk mem vec Sum Triples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Hash.lean#L99-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Hash.lean#L99-L101

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

theorem ArithmeticTriangleRemovalInVectorSpaces.mk_mem_vecSumTriples :
    (a, b, c) ∈ vecSumTriples p A B C ↔ a ∈ A ∧ b ∈ B ∧ c ∈ C ∧ ∀ r, a r + b r + c r = p - 1 := by sorry
