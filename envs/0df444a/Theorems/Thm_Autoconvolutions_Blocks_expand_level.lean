-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_expand_level
-- name    : Autoconvolutions.Blocks.expand_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:29.230801+00:00
-- url     : https://prove2.me/theorems/a3b893b0-f5f0-4c5f-9048-ce7b08af3904
-- title:
--   Blocks: expand level
-- statement:
--   The paper's `W_s B_s` written as monomials indexed by two multiplicity
--   vectors and a low digit. Independently of injectivity this polynomial identity
--   counts each selection with its exact multinomial weight.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockExpansion.lean#L72-L95
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockExpansion.lean#L72-L95

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockExpansion
set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks

theorem Autoconvolutions.Blocks.expand_level {m : ℕ} (D : ℕ) (I J : Finset (Fin m)) (u v : ℕ)
    (B : Polynomial ℝ) (hB : ∀ h, D ≤ h → B.coeff h = 0) :
    (gen D I)^u * (gen D J)^v * B =
      ∑ t ∈ rows I J u v D, monomial (rowKey D t)
        ((Nat.multinomial I t.1.1 : ℝ) * (Nat.multinomial J t.1.2 : ℝ) * B.coeff t.2) := by sorry
