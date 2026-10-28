-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_outputLaw_event_card
-- name    : CountingMatroid.Bridge.outputLaw_event_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:43:49.439158+00:00
-- url     : https://prove2.me/theorems/18d6fa3f-0887-48bc-80b0-25af0fdd3dce
-- title:
--   Output probabilities as counts of flat fair tapes
-- statement:
--   Fix any source input, feasibility implementation, and event E on rational answers paired with source cost records. Let K be repetition count times block length. The original output probability of E equals the number of length-K Boolean lists whose presampled outcome belongs to E, multiplied by 2 to the power minus K. This holds for every event and preserves the source's out-of-range false default. It converts the existing probability proof into a finite counting statement.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Analysis_SingleRunAccuracy_fairTape_event_card
import Theorems.Thm_CountingMatroid_Bridge_outputLaw_presampled

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The source probability of any output event equals its count among flat
finite Boolean tapes divided by the number of such tapes. -/
theorem CountingMatroid.Bridge.outputLaw_event_card (solver : Subroutines.FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (event : Set (ℚ × ExecutionCost)) :
    let K := (Program.schedule n p).val.repetitions * blockLength n r p
    (outputLaw solver n r o₁ o₂ p).toOuterMeasure event =
      (Set.ncard {bits : List Bool | bits.length = K ∧
        presampledOutcome solver n r o₁ o₂ p bits ∈ event} : ENNReal) *
        (1 / 2 : ENNReal)^K := by
  sorry
