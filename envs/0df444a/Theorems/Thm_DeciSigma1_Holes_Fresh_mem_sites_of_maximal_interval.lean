-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sites_of_maximal_interval
-- name    : DeciSigma1.Holes.Fresh.mem_sites_of_maximal_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:47.868186+00:00
-- url     : https://prove2.me/theorems/a60a7e23-fd89-47fe-a04c-bb9b127222be
-- title:
--   Fresh: mem sites of maximal interval
-- statement:
--   A maximal interval of deleted positions is a site.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L320-L337
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L320-L337

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {W : Fin k → List α}
variable {δ : ℕ} {cs : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.mem_sites_of_maximal_interval (hs : StrictlySeparated δ cs) {j c : ℕ} (hjc : j < c)
    (hD : ∀ p, j ≤ p → p < c → p ∈ sitePositions δ cs)
    (hj : j = 0 ∨ j - 1 ∉ sitePositions δ cs) (hc : c ∉ sitePositions δ cs) :
    j ∈ cs ∧ c = j + δ := by sorry
