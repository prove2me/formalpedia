-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_wirt_mul_fun
-- name    : Formalism.QuantumDeterminants.wirt_mul_fun
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:20:32.123054+00:00
-- url     : https://prove2.me/theorems/c5a3251c-f50c-437a-9385-f257cd74e47c
-- title:
--   Quantum Determinants: wirt mul fun
-- statement:
--   The Quantum Determinants construction uses the wirt mul fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L20-L26

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

theorem Formalism.QuantumDeterminants.wirt_mul_fun (l : Fin m) {a b : (Fin m → ℂ) → ℂ} {x : Fin m → ℂ}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    wirt l (fun y => a y * b y) x = wirt l a x * b x + a x * wirt l b x := by sorry
