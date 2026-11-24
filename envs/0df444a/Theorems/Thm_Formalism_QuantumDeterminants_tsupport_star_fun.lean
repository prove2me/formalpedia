-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_tsupport_star_fun
-- name    : Formalism.QuantumDeterminants.tsupport_star_fun
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:09.842744+00:00
-- url     : https://prove2.me/theorems/4cbeccca-f9ab-435a-9fda-10a46b1e7ce3
-- title:
--   Quantum Determinants: tsupport star fun
-- statement:
--   The Quantum Determinants construction uses the tsupport star fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L115-L119

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

theorem Formalism.QuantumDeterminants.tsupport_star_fun (g : (Fin m → ℂ) → ℂ) : tsupport (fun y => star (g y)) = tsupport g := by sorry
