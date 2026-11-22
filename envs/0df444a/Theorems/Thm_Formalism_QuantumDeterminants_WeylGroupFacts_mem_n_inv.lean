-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:57.160802+00:00
-- url     : https://prove2.me/theorems/27bef0c2-4bd5-4c9a-bd2c-5ee45cd77960
-- title:
--   Weyl Group Facts: mem n inv
-- statement:
--   The Weyl Group Facts construction uses the mem n inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L171-L175

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

theorem Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) : g⁻¹ ∈ Nset k r := by sorry
