-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_mul
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:06.453612+00:00
-- url     : https://prove2.me/theorems/a931fba7-9205-4b67-a35c-2d8ef4d80543
-- title:
--   Weyl Group Facts: mem n mul
-- statement:
--   The Weyl Group Facts construction uses the mem n mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L165-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L165-L169

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
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
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}

theorem Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) : g * h ∈ Nset k r := by sorry
