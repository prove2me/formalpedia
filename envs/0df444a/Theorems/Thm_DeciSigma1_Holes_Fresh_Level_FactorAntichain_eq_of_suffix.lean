-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_Level_FactorAntichain_eq_of_suffix
-- name    : DeciSigma1.Holes.Fresh.Level.FactorAntichain.eq_of_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:05.119087+00:00
-- url     : https://prove2.me/theorems/7b9dfc5f-2103-475c-9e9e-61b6da2a83ac
-- title:
--   Factor Antichain: eq of suffix
-- statement:
--   Two active markers ending at one cut are equal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L176-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L176-L181

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}
omit [DecidableEq α]

theorem DeciSigma1.Holes.Fresh.Level.FactorAntichain.eq_of_suffix (hA : L.FactorAntichain) {m m' : Fin k} (hm : m ∈ L.active)
    (hm' : m' ∈ L.active)
    {u : List α} (h : L.marker m <:+ u) (h' : L.marker m' <:+ u) : L.marker m = L.marker m' := by sorry
