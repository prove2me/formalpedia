-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_lt
-- name    : Formalism.QuantumDeterminants.fvec_apply_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:09.585206+00:00
-- url     : https://prove2.me/theorems/4fac1fb4-5c2a-4836-8584-12bd1e1d5873
-- title:
--   Quantum Determinants: fvec apply lt
-- statement:
--   The Quantum Determinants construction uses the fvec apply lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L93-L101

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

theorem Formalism.QuantumDeterminants.fvec_apply_lt {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (c : Fin (r + 1)) (i : Fin (2 * r + k + 1)) (hi : i.val < r) :
    fvec k r z c i = if c.val = i.val then 1 else 0 := by sorry
