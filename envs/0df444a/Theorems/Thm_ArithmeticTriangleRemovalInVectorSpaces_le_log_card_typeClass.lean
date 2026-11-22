-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_log_card_typeClass
-- name    : ArithmeticTriangleRemovalInVectorSpaces.le_log_card_typeClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:54.399802+00:00
-- url     : https://prove2.me/theorems/89dc4917-6fde-4921-bfe6-40a21f01403f
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: le log card type Class
-- statement:
--   **Lower bound for the size of a type class.** If the value `k ≤ N` appears `D k` times in
--   `a : Fin n → ℕ` and `ψ` is a positive probability vector on `range (N + 1)`, then
--   `log #(typeClass a)` is at least
--   `∑ k, D k * log (ψ k)⁻¹ - ∑ k, (D k - n * ψ k) ^ 2 / (n * ψ k) - (N + 1) * (1 + log (n + 1))`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L190-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L190-L198

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {a b b' : Fin n → ℕ}

theorem ArithmeticTriangleRemovalInVectorSpaces.le_log_card_typeClass (a : Fin n → ℕ) (ha : ∀ r, a r ≤ N) {ψ : ℕ → ℝ}
    (hψ : ∀ k ∈ range (N + 1), 0 < ψ k) (hψ₁ : ∑ k ∈ range (N + 1), ψ k = 1) :
    ∑ k ∈ range (N + 1), #{r | a r = k} * log (ψ k)⁻¹ -
        ∑ k ∈ range (N + 1), (#{r | a r = k} - n * ψ k) ^ 2 / (n * ψ k) -
        (N + 1) * (1 + log (n + 1)) ≤ log #(typeClass a) := by sorry
