-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_UW_F
-- name    : Formalism.QuantumDeterminants.UW_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:56.293194+00:00
-- url     : https://prove2.me/theorems/189eee4a-da53-43b2-a228-b7e172cd9983
-- title:
--   Quantum Determinants: UW F
-- statement:
--   The Quantum Determinants construction uses the UW F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L72-L80

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

theorem Formalism.QuantumDeterminants.UW_F {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h * Fm k r z = Fm k r z := by sorry
