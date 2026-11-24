-- Prove2me | Theorems.Thm_FockRL_Rop_apply
-- name    : FockRL.Rop_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:17.190585+00:00
-- url     : https://prove2.me/theorems/08e1ad11-65ab-4ffe-a900-ee2aa3fc2487
-- title:
--   Fock RL: Rop apply
-- statement:
--   The Fock RL construction uses the Rop apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L216-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L216-L224

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

theorem FockRL.Rop_apply (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P : FockH1Action.Pol p q r s) :
    Rop M P = ∑ l, ∑ l', if FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false then
      M l l' • (X l * (X l' * P)) else 0 := by sorry
