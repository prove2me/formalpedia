-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_gen_pow
-- name    : Autoconvolutions.Blocks.gen_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:17.125975+00:00
-- url     : https://prove2.me/theorems/59dec0b4-18d4-4b83-af2c-5055f9b0d824
-- title:
--   Blocks: gen pow
-- statement:
--   Expand the `u` independent selections of a position in `I` by their multiplicities.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockExpansion.lean#L36-L52
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockExpansion.lean#L36-L52

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

theorem Autoconvolutions.Blocks.gen_pow {m : ℕ} (D : ℕ) (I : Finset (Fin m)) (u : ℕ) :
    (gen D I)^u = ∑ a ∈ I.piAntidiag u,
      monomial (D * code D a) (Nat.multinomial I a : ℝ) := by sorry
