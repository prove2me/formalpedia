-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_mF_col
-- name    : Formalism.QuantumDeterminants.mF_col
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:49.07159+00:00
-- url     : https://prove2.me/theorems/1364e579-aa18-4391-9b27-09010177c348
-- title:
--   Quantum Determinants: m F col
-- statement:
--   The Quantum Determinants construction uses the m F col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L82-L87

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

theorem Formalism.QuantumDeterminants.mF_col {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i : Fin (2 * r + k + 1))
    (a : Fin (r + 1)) (hA : a.val < r) :
    (m * Fm k r z) i a = m i (eI k r ⟨a.val, hA⟩) := by sorry
