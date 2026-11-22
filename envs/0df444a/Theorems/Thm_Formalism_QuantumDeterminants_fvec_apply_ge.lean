-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_ge
-- name    : Formalism.QuantumDeterminants.fvec_apply_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:36.423991+00:00
-- url     : https://prove2.me/theorems/760d25fc-aaac-4431-832c-39f7957e9d96
-- title:
--   Quantum Determinants: fvec apply ge
-- statement:
--   The Quantum Determinants construction uses the fvec apply ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GroupFactorizationHolds.lean#L103-L112

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

theorem Formalism.QuantumDeterminants.fvec_apply_ge {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ)
    (c : Fin (r + 1)) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) :
    fvec k r z c i = if c.val = r then z i else 0 := by sorry
