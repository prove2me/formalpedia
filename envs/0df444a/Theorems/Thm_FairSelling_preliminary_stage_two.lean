-- Prove2me | Theorems.Thm_FairSelling_preliminary_stage_two
-- name    : FairSelling.preliminary_stage_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:56.968048+00:00
-- url     : https://prove2.me/theorems/602fc384-c51d-44c5-abc9-429e801bfd79
-- title:
--   Fair Selling: preliminary stage two
-- statement:
--   **Stage 2 of the preliminary phase.**  If no good is expensive but some agent values a good at
--   `3/4 · MMS` or more, hand that good to that agent; the other two share the rest.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/PreliminaryPhase.lean#L199-L215
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/PreliminaryPhase.lean#L199-L215

import Mathlib
import Definitions.Def_RequestProject_LemmaFourResidual
import Definitions.Def_RequestProject_PreliminaryPhase
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.preliminary_stage_two (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hcheap : ∀ i g, p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (a : Fin 3) (e : G) (hbig : (3 / 4 : ℝ) * MMS 3 (v a) p ≤ v a e) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
