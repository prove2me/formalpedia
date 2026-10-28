-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_outputLaw_presampled
-- name    : CountingMatroid.Bridge.outputLaw_presampled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:39:41.950993+00:00
-- url     : https://prove2.me/theorems/3ea5ab5a-d8af-4b47-8497-a26632ca0dbd
-- title:
--   Exact output and source-charge law under eager sampling
-- statement:
--   For every source input and feasibility implementation, the output law is exactly the pushforward of a single fair tape of length K, where K is repetition count times block length, by presampledOutcome. The equality includes rational answers and all three source counters, including early exits and aborts. These counters exclude eager tape generation and storage; the theorem asserts equality with the original source accounting, not a machine-runtime bound.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_algorithmLaw_presampled

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- Exact output-and-charge law, including early exits and aborts. The
reported charges remain the source charges, excluding eager sampling costs. -/
theorem CountingMatroid.Bridge.outputLaw_presampled (solver : Subroutines.FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams) :
    outputLaw solver n r o₁ o₂ p =
      (fairTape ((Program.schedule n p).val.repetitions * blockLength n r p)).map
        (presampledOutcome solver n r o₁ o₂ p) := by
  sorry
