-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_markerTypes_card_le_one
-- name    : DeciSigma1.Holes.Fresh.markerTypes_card_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:23.317803+00:00
-- url     : https://prove2.me/theorems/f2e7131d-80df-40c0-aaed-8ac4cc5e1b42
-- title:
--   Fresh: marker Types card le one
-- statement:
--   At each level at most one marker text ends at a given cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L132-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L132-L137

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}

theorem DeciSigma1.Holes.Fresh.markerTypes_card_le_one {r : ℕ} (u : List α) (c : ℕ) : (markerTypes W r u c).card ≤ 1 := by sorry
