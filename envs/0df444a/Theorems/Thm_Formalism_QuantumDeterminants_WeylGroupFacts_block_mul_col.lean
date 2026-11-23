-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_block_mul_col
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.block_mul_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:04.171927+00:00
-- url     : https://prove2.me/theorems/cc414305-5cf2-4a15-9762-1f25fb046c80
-- title:
--   Weyl Group Facts: block mul col
-- statement:
--   The Weyl Group Facts construction uses the block mul col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L361-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L361-L375

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

theorem Formalism.QuantumDeterminants.WeylGroupFacts.block_mul_col {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hg : col k r g) (i q : Fin (2 * r + k + 1)) (hq : q.val ≤ r + k)
    (hi : q.val ≤ i.val ∨ r ≤ i.val) : (h * g) i q = h i q := by sorry
