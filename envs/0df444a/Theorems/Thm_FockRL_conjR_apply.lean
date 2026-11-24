-- Prove2me | Theorems.Thm_FockRL_conjR_apply
-- name    : FockRL.conjR_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:23.830541+00:00
-- url     : https://prove2.me/theorems/b6ffcba0-5e67-414e-945a-340c35a390bf
-- title:
--   Fock RL: conj R apply
-- statement:
--   The Fock RL construction uses the conj R apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/KroneckerMapOneRightNeZero.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/KroneckerMapOneRightNeZero.lean#L18-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open FockRL

theorem FockRL.conjR_apply {p q : ℕ} (Z : FockH1Action.Mat p q) (a b : FockH1Action.Ix p q) :
    FockH1Action.conjR Z a b = -(jsgn a * star (Z b a) * jsgn b) := by sorry
