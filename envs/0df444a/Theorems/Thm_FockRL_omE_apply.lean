-- Prove2me | Theorems.Thm_FockRL_omE_apply
-- name    : FockRL.omE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:13.597108+00:00
-- url     : https://prove2.me/theorems/0d295b27-f8b9-4265-adeb-04ef9fa938f0
-- title:
--   Fock RL: om E apply
-- statement:
--   The Fock RL construction uses the om E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L20-L23

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

theorem FockRL.omE_apply (l l' : FockH1Action.Ln p q r s) (P : FockH1Action.Pol p q r s) :
    FockH1Action.omE l l' P = FockH1Action.raiB l (FockH1Action.lowB l' P) + if l = l' then (1 / 2 : ℂ) • P else 0 := by sorry
