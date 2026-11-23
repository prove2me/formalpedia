-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_sgn_tau
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.sgn_tau
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:32.650801+00:00
-- url     : https://prove2.me/theorems/626b2c58-0c71-4b5b-b6a8-962c4e08da6b
-- title:
--   Weyl Group Facts: sgn tau
-- statement:
--   The Weyl Group Facts construction uses the sgn tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L110-L113

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

theorem Formalism.QuantumDeterminants.WeylGroupFacts.sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by sorry
