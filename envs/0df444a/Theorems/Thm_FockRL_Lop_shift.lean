-- Prove2me | Theorems.Thm_FockRL_Lop_shift
-- name    : FockRL.Lop_shift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:56.402907+00:00
-- url     : https://prove2.me/theorems/9119ec16-4a22-41da-ad8c-5a4c3dce91e6
-- title:
--   Fock RL: Lop shift
-- statement:
--   The Fock RL construction uses the Lop shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L251-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean#L251-L260

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

theorem FockRL.Lop_shift (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (e : ℕ)
    (P : FockH1Action.Pol p q r s) :
    homogeneousComponent e (Lop M P) = Lop M (homogeneousComponent (e + 2) P) := by sorry
