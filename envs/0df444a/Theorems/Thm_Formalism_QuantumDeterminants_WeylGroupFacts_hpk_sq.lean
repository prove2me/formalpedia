-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:15.846015+00:00
-- url     : https://prove2.me/theorems/5fc2ebde-80aa-441d-905e-f39f836fcf19
-- title:
--   Weyl Group Facts: hpk sq
-- statement:
--   The Weyl Group Facts construction uses the hpk sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L119-L125

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

theorem Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq : Hpk k r * Hpk k r = 1 := by sorry
