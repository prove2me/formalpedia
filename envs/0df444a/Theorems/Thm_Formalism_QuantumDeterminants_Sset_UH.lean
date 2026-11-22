-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_Sset_UH
-- name    : Formalism.QuantumDeterminants.Sset_UH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:03.55382+00:00
-- url     : https://prove2.me/theorems/9f5c362e-7871-4bdd-adc9-179bc08ae4c5
-- title:
--   Quantum Determinants: Sset UH
-- statement:
--   The Quantum Determinants construction uses the Sset UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L62-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L62-L70

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

theorem Formalism.QuantumDeterminants.Sset_UH {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ Sset k r z) :
    sᴴ * Hpk k r * s = Hpk k r := by sorry
