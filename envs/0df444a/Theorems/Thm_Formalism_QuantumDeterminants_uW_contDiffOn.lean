-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_uW_contDiffOn
-- name    : Formalism.QuantumDeterminants.uW_contDiffOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:09.370063+00:00
-- url     : https://prove2.me/theorems/74ed2a9d-4b99-4ff6-9602-378e39bd34eb
-- title:
--   Quantum Determinants: u W cont Diff On
-- statement:
--   The Quantum Determinants construction uses the u W cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L82-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L82-L102

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

theorem Formalism.QuantumDeterminants.uW_contDiffOn (l : Fin m) : ContDiffOn ℝ ∞ (uW l) (OmX m) := by sorry
