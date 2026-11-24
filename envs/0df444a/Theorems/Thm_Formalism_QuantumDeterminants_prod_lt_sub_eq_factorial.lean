-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_prod_lt_sub_eq_factorial
-- name    : Formalism.QuantumDeterminants.prod_lt_sub_eq_factorial
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:59.229424+00:00
-- url     : https://prove2.me/theorems/258d2415-315b-4172-a439-e9dbbf84fc83
-- title:
--   Quantum Determinants: prod lt sub eq factorial
-- statement:
--   The Quantum Determinants construction uses the prod lt sub eq factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/HolomorphicLowKDimensionHolds.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/HolomorphicLowKDimensionHolds.lean#L23-L38

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

theorem Formalism.QuantumDeterminants.prod_lt_sub_eq_factorial {n : ℕ} (b : Fin n) :
    ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      (((b : ℕ).factorial : ℕ) : ℝ) := by sorry
