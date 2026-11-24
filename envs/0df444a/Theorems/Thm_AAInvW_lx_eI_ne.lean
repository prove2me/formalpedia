-- Prove2me | Theorems.Thm_AAInvW_lx_eI_ne
-- name    : AAInvW.lx_eI_ne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:04:32.053671+00:00
-- url     : https://prove2.me/theorems/38d8c182-5612-4f6e-8beb-0f8fce9aeca1
-- title:
--   AAInv W: lx e I ne
-- statement:
--   The AAInv W construction uses the lx e I ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L57-L61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem AAInvW.lx_eI_ne (k r : ℕ) (b c : Fin r) (h : b.val ≠ c.val) : eI k r b ≠ eI k r c := by sorry
