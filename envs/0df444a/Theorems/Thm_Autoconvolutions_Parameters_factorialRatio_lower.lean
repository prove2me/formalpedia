-- Prove2me | Theorems.Thm_Autoconvolutions_Parameters_factorialRatio_lower
-- name    : Autoconvolutions.Parameters.factorialRatio_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:21.466279+00:00
-- url     : https://prove2.me/theorems/9a197373-f7d8-4708-b0b3-10633118ad07
-- title:
--   Parameters: factorial Ratio lower
-- statement:
--   A quantitative form of the factorial product estimate, for any
--   displacement through the central index.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Parameters.lean#L52-L69
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Parameters.lean#L52-L69

module
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Parameters
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Parameters

theorem Autoconvolutions.Parameters.factorialRatio_lower {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    1 - (j : ℝ)^2 / N ≤ factorialRatio N j := by sorry
