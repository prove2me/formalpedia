-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_of_fix
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.col_of_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:26.332849+00:00
-- url     : https://prove2.me/theorems/6f84c120-7cf5-4866-b22c-ffd669636266
-- title:
--   Weyl Group Facts: col of fix
-- statement:
--   The Weyl Group Facts construction uses the col of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L257-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L257-L267

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

theorem Formalism.QuantumDeterminants.WeylGroupFacts.col_of_fix {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {c : Fin (2 * r + k + 1)} (hc : h *ᵥ bvec c = bvec c) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by sorry
