-- Prove2me | Theorems.Thm_FockRL_fi_add_left
-- name    : FockRL.fi_add_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:28.747925+00:00
-- url     : https://prove2.me/theorems/27c4e074-a343-42b3-8e50-aca995fca95b
-- title:
--   Fock RL: fi add left
-- statement:
--   The Fock RL construction uses the fi add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L284-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L284-L288

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

theorem FockRL.fi_add_left (hL : FockLinL) (P₁ P₂ Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (P₁ + P₂) Q = FockH1Action.fockInner P₁ Q + FockH1Action.fockInner P₂ Q := by sorry
