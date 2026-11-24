-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_wirt_star_fun
-- name    : Formalism.QuantumDeterminants.wirt_star_fun
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:20:33.751463+00:00
-- url     : https://prove2.me/theorems/b890ad56-44a5-4912-9a1e-82c1de36c513
-- title:
--   Quantum Determinants: wirt star fun
-- statement:
--   The Quantum Determinants construction uses the wirt star fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L28-L35

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

theorem Formalism.QuantumDeterminants.wirt_star_fun (l : Fin m) (g : (Fin m → ℂ) → ℂ) (x : Fin m → ℂ) :
    wirt l (fun y => star (g y)) x = star (wirtBar l g x) := by sorry
