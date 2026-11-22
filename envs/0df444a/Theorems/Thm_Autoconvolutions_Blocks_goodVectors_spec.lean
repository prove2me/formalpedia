-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_goodVectors_spec
-- name    : Autoconvolutions.Blocks.goodVectors_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:37.745799+00:00
-- url     : https://prove2.me/theorems/46101212-53b9-4916-b7ca-6d9b0963f316
-- title:
--   Blocks: good Vectors spec
-- statement:
--   The Blocks construction uses the good Vectors spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Occupancy.lean#L39-L55
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Occupancy.lean#L39-L55

module
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_Autoconvolutions_Occupancy
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Blocks
variable {ι : Type*} [DecidableEq ι]

theorem Autoconvolutions.Blocks.goodVectors_spec {I : Finset ι} {k : ℕ} {a : ι → ℕ} (ha : a ∈ goodVectors I k) :
    a ∈ I.piAntidiag k ∧ ∀ i, a i ≤ 1 := by sorry
