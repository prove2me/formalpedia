-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_prefixComparingCuts_le
-- name    : DeciSigma1.Holes.Fresh.card_prefixComparingCuts_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:48.796694+00:00
-- url     : https://prove2.me/theorems/5e358279-dd44-44c8-b76d-19940e8cd289
-- title:
--   Fresh: card prefix Comparing Cuts le
-- statement:
--   A fixed text has at most `N - 1` nonempty suffixes of a fresh word as prefixes: their
--   starting cuts carry distinct live states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L736-L766
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L736-L766

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
variable [DecidableEq α]
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]

theorem DeciSigma1.Holes.Fresh.card_prefixComparingCuts_le {T : Table α S k} {W : Fin k → List α} {j : Fin k}
    (hj : T.Fresh W j)
    (txt : List α) :
    ((range (W j).length).filter (fun b => (W j).drop b <+: txt)).card ≤ Fintype.card S - 1 := by sorry
