-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_of_left_inv
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.col_of_left_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:11.152586+00:00
-- url     : https://prove2.me/theorems/55a36205-d0e0-4d41-bd99-c69a7aab2874
-- title:
--   Weyl Group Facts: col of left inv
-- statement:
--   The Weyl Group Facts construction uses the col of left inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L60-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L60-L82

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

theorem Formalism.QuantumDeterminants.WeylGroupFacts.col_of_left_inv {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hm : g' * g = 1) : col k r g' := by sorry
