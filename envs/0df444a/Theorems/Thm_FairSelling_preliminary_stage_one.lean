-- Prove2me | Theorems.Thm_FairSelling_preliminary_stage_one
-- name    : FairSelling.preliminary_stage_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:35.150415+00:00
-- url     : https://prove2.me/theorems/11806ce7-4afe-40a0-b59b-2e21e98560a0
-- title:
--   Fair Selling: preliminary stage one
-- statement:
--   **Stage 1 of the preliminary phase.**  If some good is worth (in price!) at least
--   `3/4 · MMS` to some agent, then a complete `3/4`-MMS allocation exists: sell that good, pay the
--   agent of least maximin share, and let the other two agents share the rest.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/PreliminaryPhase.lean#L171-L195
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/PreliminaryPhase.lean#L171-L195

import Mathlib
import Definitions.Def_RequestProject_LemmaFourResidual
import Definitions.Def_RequestProject_PreliminaryPhase
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.preliminary_stage_one (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (i0 : Fin 3) (e : G) (hbig : (3 / 4 : ℝ) * MMS 3 (v i0) p ≤ p e) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
