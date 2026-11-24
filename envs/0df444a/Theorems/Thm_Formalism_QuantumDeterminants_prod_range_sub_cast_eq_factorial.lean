-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_prod_range_sub_cast_eq_factorial
-- name    : Formalism.QuantumDeterminants.prod_range_sub_cast_eq_factorial
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:15.606323+00:00
-- url     : https://prove2.me/theorems/39d939df-375a-46aa-8ec3-f214b110b052
-- title:
--   Quantum Determinants: prod range sub cast eq factorial
-- statement:
--   The Quantum Determinants construction uses the prod range sub cast eq factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/HolomorphicLowKDimensionHolds.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/HolomorphicLowKDimensionHolds.lean#L12-L21

import Definitions.Def_Formalism_FormalDegreeBessel_HolDimLowK
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_HolomorphicLowKDimensionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL

theorem Formalism.QuantumDeterminants.prod_range_sub_cast_eq_factorial (b : ℕ) :
    ∏ j ∈ range b, ((b : ℝ) - (j : ℝ)) = (b.factorial : ℝ) := by sorry
