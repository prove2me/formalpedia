-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_tau
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.tau_tau
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:05.849042+00:00
-- url     : https://prove2.me/theorems/d76d43cd-aa99-47f9-ae49-e7b0d2932ddd
-- title:
--   Weyl Group Facts: tau tau
-- statement:
--   The Weyl Group Facts construction uses the tau tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L104-L108

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

theorem Formalism.QuantumDeterminants.WeylGroupFacts.tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by sorry
