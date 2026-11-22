-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_isOpen_OmX
-- name    : Formalism.QuantumDeterminants.isOpen_OmX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:27.969744+00:00
-- url     : https://prove2.me/theorems/3573e882-7b10-456f-89c3-ef23e0db2d25
-- title:
--   Quantum Determinants: is Open Om X
-- statement:
--   The Quantum Determinants construction uses the is Open Om X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L11-L16

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

theorem Formalism.QuantumDeterminants.isOpen_OmX (m : ℕ) : IsOpen (OmX m) := by sorry
