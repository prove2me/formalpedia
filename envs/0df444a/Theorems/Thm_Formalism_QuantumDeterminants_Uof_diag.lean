-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_Uof_diag
-- name    : Formalism.QuantumDeterminants.Uof_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:03.711805+00:00
-- url     : https://prove2.me/theorems/a2a8dc13-16f5-4d8e-8208-0f38feec142d
-- title:
--   Quantum Determinants: Uof diag
-- statement:
--   The Quantum Determinants construction uses the Uof diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L182-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L182-L189

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

theorem Formalism.QuantumDeterminants.Uof_diag {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r)
    (c : Fin (r + 1)) : Uof k r z m c c = 1 := by sorry
