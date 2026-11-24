-- Prove2me | Theorems.Thm_FockRL_fi_smul_left
-- name    : FockRL.fi_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:27.249802+00:00
-- url     : https://prove2.me/theorems/de686476-99e6-460e-899c-3895074c1c63
-- title:
--   Fock RL: fi smul left
-- statement:
--   The Fock RL construction uses the fi smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L278-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L278-L282

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

theorem FockRL.fi_smul_left (hL : FockLinL) (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (c • P) Q = (starRingEnd ℂ) c * FockH1Action.fockInner P Q := by sorry
