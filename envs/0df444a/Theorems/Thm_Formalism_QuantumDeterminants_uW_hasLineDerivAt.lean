-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_uW_hasLineDerivAt
-- name    : Formalism.QuantumDeterminants.uW_hasLineDerivAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:07.597835+00:00
-- url     : https://prove2.me/theorems/441f5c8d-88e8-4951-9315-295ddc878d14
-- title:
--   Quantum Determinants: u W has Line Deriv At
-- statement:
--   The Quantum Determinants construction uses the u W has Line Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L61-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L61-L80

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

theorem Formalism.QuantumDeterminants.uW_hasLineDerivAt (l : Fin m) (x : Fin m → ℂ) (hx : x l ≠ 0) (a : ℂ) :
    HasLineDerivAt ℝ (uW l) (-(star a) / (star (x l)) ^ 2 *
      (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)) x (Pi.single l a) := by sorry
