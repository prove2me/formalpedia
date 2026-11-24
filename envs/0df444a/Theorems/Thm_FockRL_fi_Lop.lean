-- Prove2me | Theorems.Thm_FockRL_fi_Lop
-- name    : FockRL.fi_Lop
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:26.978307+00:00
-- url     : https://prove2.me/theorems/c86e0e89-25bc-45f5-9a1f-c6d401c20e9c
-- title:
--   Fock RL: fi Lop
-- statement:
--   The Fock RL construction uses the fi Lop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L340-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L340-L350

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

theorem FockRL.fi_Lop (hR : FockLinR)
    (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P Q : FockH1Action.Pol p q r s) :
    FockH1Action.fockInner P (Lop M Q) = ∑ l, ∑ l', if FockH1Action.linePos l = false ∧ FockH1Action.linePos l' = true
      then -(M l l' * FockH1Action.fockInner P (pderiv l (pderiv l' Q))) else 0 := by sorry
