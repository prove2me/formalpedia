-- Prove2me | Theorems.Thm_FockRL_fi_Rop
-- name    : FockRL.fi_Rop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:21.290795+00:00
-- url     : https://prove2.me/theorems/d9d4ddd7-b43d-4e21-a28b-874b2b5755a7
-- title:
--   Fock RL: fi Rop
-- statement:
--   The Fock RL construction uses the fi Rop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L328-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L328-L338

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

theorem FockRL.fi_Rop (hL : FockLinL) (hX : FockXAdj)
    (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P Q : FockH1Action.Pol p q r s) :
    FockH1Action.fockInner (Rop M P) Q = ∑ l, ∑ l', if FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false
      then (starRingEnd ℂ) (M l l') * FockH1Action.fockInner P (pderiv l' (pderiv l Q)) else 0 := by sorry
