-- Prove2me | Theorems.Thm_FockRL_Rop_raise
-- name    : FockRL.Rop_raise
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:01.52669+00:00
-- url     : https://prove2.me/theorems/75e03493-ea29-40a1-914c-0dffed1f7c85
-- title:
--   Fock RL: Rop raise
-- statement:
--   The Fock RL construction uses the Rop raise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L236-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L236-L245

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open FockRL
variable {p q r s : ℕ}

theorem FockRL.Rop_raise (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (d : ℕ)
    (P : FockH1Action.Pol p q r s) (hP : P ∈ FockH1Action.homog (FockH1Action.Ln p q r s) d) :
    Rop M P ∈ FockH1Action.homog (FockH1Action.Ln p q r s) (d + 2) := by sorry
