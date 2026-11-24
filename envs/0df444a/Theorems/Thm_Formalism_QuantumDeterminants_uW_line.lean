-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_uW_line
-- name    : Formalism.QuantumDeterminants.uW_line
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:30.579889+00:00
-- url     : https://prove2.me/theorems/591576af-680d-4dc9-acaf-41b7d88492fb
-- title:
--   Quantum Determinants: u W line
-- statement:
--   The Quantum Determinants construction uses the u W line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L39-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L39-L59

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ}

theorem Formalism.QuantumDeterminants.uW_line (l : Fin m) (x : Fin m → ℂ) (a : ℂ) (t : ℝ) :
    uW l (x + t • (Pi.single l a : Fin m → ℂ)) = (star (x l) + (t : ℂ) * star a)⁻¹ *
      (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) := by sorry
