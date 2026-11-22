-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_exists_isMulticoloredSumFree_of_hash
-- name    : ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_of_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:57.046091+00:00
-- url     : https://prove2.me/theorems/5e8c4fd8-1bb4-4f57-9809-3815d964f2ff
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: exists is Multicolored Sum Free of hash
-- statement:
--   **Lemma 4.6 of Kleinberg, Sawin and Speyer.** Some hash leaves at least
--   `#V * #S * (P - F) / P ^ 3` isolated triples, which form a multicolored sum-free family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Hash.lean#L417-L439
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Hash.lean#L417-L439

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

theorem ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_of_hash [Fact P.Prime] (hp : 2 ≤ p) (hpP : p < P)
    (hsum : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ∑ r, (a r + b r + c r) = n * (p - 1))
    (hF : ∀ v ∈ vecSumTriples p A B C, #{v' ∈ vecSumTriples p A B C | Shares v v'} ≤ F)
    (hS : ThreeAPFree (S : Set (ZMod P))) :
    ∃ (m : ℕ) (x y z : Fin m → Fin n → ZMod p), IsMulticoloredSumFree x y z ∧
      #(vecSumTriples p A B C) * #S * (P - F : ℝ) ≤ m * P ^ 3 := by sorry
