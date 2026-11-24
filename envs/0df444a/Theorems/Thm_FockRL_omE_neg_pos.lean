-- Prove2me | Theorems.Thm_FockRL_omE_neg_pos
-- name    : FockRL.omE_neg_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:35.178807+00:00
-- url     : https://prove2.me/theorems/758a7583-6ff4-4949-924e-2f45dd59b46b
-- title:
--   Fock RL: om E neg pos
-- statement:
--   The Fock RL construction uses the om E neg pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L63-L69

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

theorem FockRL.omE_neg_pos {l l' : FockH1Action.Ln p q r s} (h1 : FockH1Action.linePos l = false)
    (h2 : FockH1Action.linePos l' = true) (P : FockH1Action.Pol p q r s) :
    FockH1Action.omE l l' P = -(pderiv l (pderiv l' P)) := by sorry
