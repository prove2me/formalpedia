-- Prove2me | Theorems.Thm_AAInvW_lx_esI_ne
-- name    : AAInvW.lx_esI_ne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:04:50.835919+00:00
-- url     : https://prove2.me/theorems/cd5702fb-d2eb-4a61-be30-be89c2d0b49c
-- title:
--   AAInv W: lx es I ne
-- statement:
--   The AAInv W construction uses the lx es I ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L49-L55

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

theorem AAInvW.lx_esI_ne (k r : ℕ) (b c : Fin r) (h : b.val ≠ c.val) : esI k r b ≠ esI k r c := by sorry
