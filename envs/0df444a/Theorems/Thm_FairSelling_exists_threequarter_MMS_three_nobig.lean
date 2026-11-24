-- Prove2me | Theorems.Thm_FairSelling_exists_threequarter_MMS_three_nobig
-- name    : FairSelling.exists_threequarter_MMS_three_nobig
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:39.633657+00:00
-- url     : https://prove2.me/theorems/929ae316-1a2f-477e-a92c-f574f87ab387
-- title:
--   Fair Selling: exists threequarter MMS three nobig
-- statement:
--   **The `n = 3`, `3/4`-MMS theorem after the preliminary phase.**  If no agent values any good at
--   `3/4 · MMS` or more, three agents admit a valid allocation giving everybody at least
--   `3/4 · MMS`, assuming only the residual case of Lemma 4 (which is discharged in
--   `RequestProject.LemmaFourResidual`, giving the unconditional
--   `exists_threequarter_MMS_three_nobig'`).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L415-L426
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L415-L426

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.exists_threequarter_MMS_three_nobig (hL4 : LemmaFourCashSold G)
    (v : Fin 3 → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
