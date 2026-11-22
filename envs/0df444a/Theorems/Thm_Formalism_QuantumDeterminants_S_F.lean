-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_S_F
-- name    : Formalism.QuantumDeterminants.S_F
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:52.470064+00:00
-- url     : https://prove2.me/theorems/5fe5a3e3-1b78-49f0-bdf8-f8a75afc16a2
-- title:
--   Quantum Determinants: S F
-- statement:
--   The Quantum Determinants construction uses the S F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L191-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L191-L197

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

theorem Formalism.QuantumDeterminants.S_F {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ Sset k r z) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, (∀ c a, a < c → U c a = 0) ∧ (∀ c, U c c = 1) ∧
      s * Fm k r z = Fm k r z * U := by sorry
