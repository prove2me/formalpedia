-- Prove2me | Theorems.Thm_FairSelling_SEFX_full_of_EFX_of_money_extension
-- name    : FairSelling.SEFX_full_of_EFX_of_money_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:16:14.057486+00:00
-- url     : https://prove2.me/theorems/1bebcc2d-86d1-4bee-8b93-b38ad372100b
-- title:
--   Fair Selling: SEFX full of EFX of money extension
-- statement:
--   **Lemma 10, direction `EFX ⟹ SEFX` (full allocations).**  With the whole sale proceeds
--   distributed, the construction needs in addition a distribution `P` of the proceeds under which no
--   agent envies a money-holding agent.  This is the extension result for mixed divisible and
--   indivisible goods quoted by the manuscript, which is *assumed* here (as an explicit hypothesis,
--   `hext`) rather than proved.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L311-L344
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L311-L344

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
variable {v p sellable A}

theorem FairSelling.SEFX_full_of_EFX_of_money_extension (hv : ∀ i g, 0 ≤ v i g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hA : IsPartitionOf A (Finset.univ \ sellable)) (hEFX : EFXalloc v A)
    (hext : ∃ P : Fin n → ℝ, (∀ j, 0 ≤ P j) ∧ (∑ j, P j = ∑ g ∈ sellable, p g) ∧
      ∀ i j, 0 < P j → (∑ g' ∈ A i, v i g') + P i ≥ (∑ g' ∈ A j, v i g') + P j) :
    ∃ o : Outcome G n, o.Full p sellable ∧ SEFX v p o := by sorry
