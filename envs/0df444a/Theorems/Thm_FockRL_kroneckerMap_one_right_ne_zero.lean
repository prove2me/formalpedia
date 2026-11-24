-- Prove2me | Theorems.Thm_FockRL_kroneckerMap_one_right_ne_zero
-- name    : FockRL.kroneckerMap_one_right_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:37.869609+00:00
-- url     : https://prove2.me/theorems/cf1c0ca3-cbba-4b99-b241-2bd645b72daf
-- title:
--   Fock RL: kronecker Map one right ne zero
-- statement:
--   The Fock RL construction uses the kronecker Map one right ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/KroneckerMapOneRightNeZero.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/KroneckerMapOneRightNeZero.lean#L60-L66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open FockRL

theorem FockRL.kroneckerMap_one_right_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat p q) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s) (a, b) (a', b') ≠ 0) :
    Z a a' ≠ 0 ∧ b = b' := by sorry
