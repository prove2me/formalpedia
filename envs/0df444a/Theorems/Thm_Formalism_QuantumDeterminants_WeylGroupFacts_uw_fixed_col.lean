-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_fixed_col
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.uw_fixed_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:16.890813+00:00
-- url     : https://prove2.me/theorems/ec36aef9-fa02-4ba5-9951-2d48be926c31
-- title:
--   Weyl Group Facts: uw fixed col
-- statement:
--   The Weyl Group Facts construction uses the uw fixed col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L296-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L296-L315

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

theorem Formalism.QuantumDeterminants.WeylGroupFacts.uw_fixed_col {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by sorry
