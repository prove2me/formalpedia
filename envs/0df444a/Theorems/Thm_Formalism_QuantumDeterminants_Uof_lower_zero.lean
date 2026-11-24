-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_Uof_lower_zero
-- name    : Formalism.QuantumDeterminants.Uof_lower_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:12.187988+00:00
-- url     : https://prove2.me/theorems/dc2425b6-bf73-4dd0-8da4-f2dd88eaf4ee
-- title:
--   Quantum Determinants: Uof lower zero
-- statement:
--   The Quantum Determinants construction uses the Uof lower zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L166-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L166-L180

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants

theorem Formalism.QuantumDeterminants.Uof_lower_zero {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r)
    (c a : Fin (r + 1)) (hac : a < c) : Uof k r z m c a = 0 := by sorry
