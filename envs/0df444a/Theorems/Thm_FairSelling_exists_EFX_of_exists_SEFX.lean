-- Prove2me | Theorems.Thm_FairSelling_exists_EFX_of_exists_SEFX
-- name    : FairSelling.exists_EFX_of_exists_SEFX
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:15:51.461359+00:00
-- url     : https://prove2.me/theorems/c15aabdc-a1f6-4ff2-95f6-5a91f16b988a
-- title:
--   Fair Selling: exists EFX of exists SEFX
-- statement:
--   **Lemma 10, direction `SEFX ⟹ EFX`.**  If every instance with sellable goods admits a full
--   `SEFX` allocation, then every instance without selling admits an `EFX` allocation.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L147-L153
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L147-L153

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.exists_EFX_of_exists_SEFX
    (hSEFX : ∀ w : Fin n → G → ℝ, (∀ i g, 0 ≤ w i g) →
      ∃ o : Outcome G n, o.Full (fun _ => 0) ∅ ∧ SEFX w (fun _ => 0) o)
    (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ A : Fin n → Finset G, IsPartitionOf A Finset.univ ∧ EFXalloc v A := by sorry
