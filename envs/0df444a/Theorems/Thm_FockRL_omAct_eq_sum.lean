-- Prove2me | Theorems.Thm_FockRL_omAct_eq_sum
-- name    : FockRL.omAct_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:28.433918+00:00
-- url     : https://prove2.me/theorems/e26fa4c5-fddd-4355-9515-610a8e0ecf3c
-- title:
--   Fock RL: om Act eq sum
-- statement:
--   The Fock RL construction uses the om Act eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L12-L18

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

theorem FockRL.omAct_eq_sum (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) :
    FockH1Action.omAct p q r s M = ∑ l, ∑ l', M l l' • FockH1Action.omE l l' := by sorry
