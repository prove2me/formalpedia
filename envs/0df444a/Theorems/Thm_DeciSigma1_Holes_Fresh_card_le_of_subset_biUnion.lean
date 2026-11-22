-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_card_le_of_subset_biUnion
-- name    : DeciSigma1.Holes.Fresh.card_le_of_subset_biUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:11.017134+00:00
-- url     : https://prove2.me/theorems/ca091a2e-9f0b-4eb7-b5bd-2e75bb9030d3
-- title:
--   Fresh: card le of subset bi Union
-- statement:
--   A family of positions, each read as a nonempty suffix of a coordinate word that is a
--   prefix of `z`, has at most `k (N - 1)` members.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L774-L783
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L774-L783

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

theorem DeciSigma1.Holes.Fresh.card_le_of_subset_biUnion {T : Table α S k} {W : Fin k → List α}
    (hfr : ∀ i, T.Fresh W i) (z : List α) (f : Fin k → ℕ → ℕ) {P : Finset ℕ}
    (hP : P ⊆ univ.biUnion (fun j => (suffixOccurrenceCuts W j z).image (f j))) :
    P.card ≤ k * (Fintype.card S - 1) := by sorry
