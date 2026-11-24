-- Prove2me | Theorems.Thm_FockRL_fi_add_right
-- name    : FockRL.fi_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:35.255058+00:00
-- url     : https://prove2.me/theorems/5fb69cc2-cb0a-4dc3-8f5e-536e7e1a9c3f
-- title:
--   Fock RL: fi add right
-- statement:
--   The Fock RL construction uses the fi add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L296-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L296-L300

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
variable {σ : Type}

theorem FockRL.fi_add_right (hR : FockLinR) (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (Q₁ + Q₂) = FockH1Action.fockInner P Q₁ + FockH1Action.fockInner P Q₂ := by sorry
