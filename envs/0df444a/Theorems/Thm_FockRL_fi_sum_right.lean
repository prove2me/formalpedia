-- Prove2me | Theorems.Thm_FockRL_fi_sum_right
-- name    : FockRL.fi_sum_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:20.748363+00:00
-- url     : https://prove2.me/theorems/152f70d8-d021-45bf-a2c9-aab52711bd16
-- title:
--   Fock RL: fi sum right
-- statement:
--   The Fock RL construction uses the fi sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L317-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L317-L324

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

theorem FockRL.fi_sum_right {ι : Type} (hR : FockLinR) (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (P : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, FockH1Action.fockInner P (f i) := by sorry
