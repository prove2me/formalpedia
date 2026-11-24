-- Prove2me | Theorems.Thm_FockRL_fi_sum_left
-- name    : FockRL.fi_sum_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:31.698677+00:00
-- url     : https://prove2.me/theorems/10a07190-ac64-4490-bf96-b8e18d25fbf9
-- title:
--   Fock RL: fi sum left
-- statement:
--   The Fock RL construction uses the fi sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L302-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L302-L309

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

theorem FockRL.fi_sum_left {ι : Type} (hL : FockLinL) (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, FockH1Action.fockInner (f i) Q := by sorry
