-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_dslowk_lowK_eq
-- name    : Formalism.QuantumDeterminants.dslowk_lowK_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:56.934998+00:00
-- url     : https://prove2.me/theorems/bac2f33f-a1a3-40a2-a50e-b33fca6bc1db
-- title:
--   Quantum Determinants: dslowk low K eq
-- statement:
--   The Quantum Determinants construction uses the dslowk low K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/DSLowK.lean#L23-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/DSLowK.lean#L23-L44

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
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

theorem Formalism.QuantumDeterminants.dslowk_lowK_eq {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK ε lam a = lam a + (((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)) - 2 * rhoC ε a := by sorry
